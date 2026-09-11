// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL CDC FIFO (Internal 1R1W Flop-RAM, Push Credit/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_flops_push_credit_fpv_monitor #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int MaxCredit = Depth,
    parameter bit RegisterPushOutputs = 0,
    parameter bit RegisterPopOutputs = 1,
    parameter int NumSyncStages = 3,
    parameter int FlopRamDepthTiles = 1,
    parameter int FlopRamWidthTiles = 1,
    parameter int FlopRamAddressDepthStages = 0,
    parameter int FlopRamReadDataDepthStages = 0,
    parameter int FlopRamReadDataWidthStages = 0,
    parameter bit EnableStructuredGatesDataQualification = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    // DUT clk & rst
    input logic push_clk,
    input logic push_rst,
    input logic pop_clk,
    input logic pop_rst,

    // Push-side interface
    input logic             push_sender_in_reset,
    input logic             push_credit_stall,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic pop_ready,

    // Push-side credits
    input logic [CreditWidth-1:0] credit_initial_push,
    input logic [CreditWidth-1:0] credit_withhold_push
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;

  // DUT primary outputs
  logic                   push_receiver_in_reset;
  logic                   push_credit;
  logic                   pop_valid;
  logic [      Width-1:0] pop_data;
  // Push-side credits
  logic [CreditWidth-1:0] credit_count_push;
  logic [CreditWidth-1:0] credit_available_push;
  // Push-side status flags
  logic                   push_full;
  logic [ CountWidth-1:0] push_slots;
  // Pop-side status flags
  logic                   pop_empty;
  logic [ CountWidth-1:0] pop_items;

  logic                   push_either_rst;
  logic                   fv_rst;

  assign push_either_rst = push_rst || push_sender_in_reset;
  // A coordinated reset retires pending reference transactions and restarts
  // the FIFO counters. New pushes remain idle until all reset inputs deassert.
  assign fv_rst = rst || push_either_rst || pop_rst;

  // ----------Instantiate DUT----------
  br_cdc_fifo_flops_push_credit #(
      .Depth(Depth),
      .ValidateDepthSupportsFullBandwidth(0),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumSyncStages(NumSyncStages),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableStructuredGatesDataQualification(EnableStructuredGatesDataQualification),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) dut (
      .push_clk,
      .push_rst,
      .pop_clk,
      .pop_rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .push_full,
      .push_slots,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .pop_empty,
      .pop_items
  );

  // ----------Instantiate credit FV checker----------
  br_credit_receiver_fpv_monitor #(
      .MaxCredit(MaxCredit)
  ) fv_credit_receiver (
      .clk(push_clk),
      // The modeled sender credit balance clears on either push-side reset.
      .rst(push_either_rst),
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .config_base('d0),
      .config_bound('d0)
  );

  // ----------Instantiate CDC FIFO FV basic checks----------
  br_cdc_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(0),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency)
  ) fv_checker (
      .clk,
      .rst(fv_rst),
      .push_clk,
      .push_rst(fv_rst),
      .push_ready(1'd1),
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst(fv_rst),
      .pop_ready,
      .pop_valid(pop_valid && !fv_rst),
      .pop_data,
      .push_full,
      .push_slots,
      .pop_empty,
      .pop_items
  );

  `BR_ASSERT_CR(no_valid_data_stable_a, ##1 !pop_valid && !$fell(pop_valid) |-> $stable(pop_data),
                pop_clk, fv_rst)

  // Reach sender reset after all data and credits have returned, while the
  // completed-pop history is large enough to expose a stale-count delta.
  // verilog_format: off
  `BR_COVER_CR(sender_reset_after_drained_fifo_c,
               (!fv_rst && !push_valid && pop_empty && !pop_valid && push_slots == Depth &&
                credit_initial_push == Depth && fv_credit_receiver.fv_credit_cnt == Depth &&
                dut.br_cdc_fifo_ctrl_1r1w_push_credit.
                    br_cdc_fifo_ctrl_push_1r1w_push_credit_inst.br_cdc_fifo_push_ctrl_credit.
                    br_cdc_fifo_push_flag_mgr.pop_count_saved > Depth)
               ##1 (!push_rst && push_sender_in_reset && !pop_rst)
               ##1 (!push_rst && push_sender_in_reset && !pop_rst), push_clk, rst)
  // verilog_format: on

endmodule : br_cdc_fifo_flops_push_credit_fpv_monitor
