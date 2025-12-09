// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL FIFO (Internal 1R1W Flop-RAM, Push Credit/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_flops_push_credit_fpv_monitor #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    parameter int MaxCredit = Depth,
    parameter bit RegisterPushOutputs = 0,
    parameter bit RegisterPopOutputs = 1,
    parameter int FlopRamDepthTiles = 1,
    parameter int FlopRamWidthTiles = 1,
    parameter int FlopRamAddressDepthStages = 0,
    parameter int FlopRamReadDataDepthStages = 0,
    parameter int FlopRamReadDataWidthStages = 0,
    parameter bit EnableCoverCreditWithhold = 1,
    parameter bit EnableCoverPushSenderInReset = 1,
    parameter bit EnableCoverPushCreditStall = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic             push_sender_in_reset,
    input logic             push_receiver_in_reset,
    input logic             push_credit_stall,
    input logic             push_credit,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic                  full,
    input logic                  full_next,
    input logic [CountWidth-1:0] slots,
    input logic [CountWidth-1:0] slots_next,

    // Push-side credits
    input logic [CreditWidth-1:0] credit_initial_push,
    input logic [CreditWidth-1:0] credit_withhold_push,
    input logic [CreditWidth-1:0] credit_count_push,
    input logic [CreditWidth-1:0] credit_available_push,

    // Pop-side status flags
    input logic                  empty,
    input logic                  empty_next,
    input logic [CountWidth-1:0] items,
    input logic [CountWidth-1:0] items_next
);

  // ----------Instantiate credit FV checker----------
  br_credit_receiver_fpv_monitor #(
      .PStatic(0),
      .MaxCredit(MaxCredit),
      .NumWritePorts(1),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall)
  ) br_credit_receiver_fpv_monitor (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .config_base ('d0),
      .config_bound('d0)
  );

  // ----------Instantiate non-credit version FV checker----------
  br_fifo_flops_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .EnableCoverPushBackpressure(0),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages)
  ) br_fifo_flops_fpv_monitor (
      .clk,
      .rst,
      .push_ready(1'd1),
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .empty,
      .empty_next,
      .items,
      .items_next
  );

endmodule : br_fifo_flops_push_credit_fpv_monitor

bind br_fifo_flops_push_credit br_fifo_flops_push_credit_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .EnableBypass(EnableBypass),
    .MaxCredit(MaxCredit),
    .RegisterPushOutputs(RegisterPushOutputs),
    .RegisterPopOutputs(RegisterPopOutputs),
    .FlopRamDepthTiles(FlopRamDepthTiles),
    .FlopRamWidthTiles(FlopRamWidthTiles),
    .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
    .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
    .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
    .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
    .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
    .EnableCoverPushCreditStall(EnableCoverPushCreditStall)
) monitor (.*);
