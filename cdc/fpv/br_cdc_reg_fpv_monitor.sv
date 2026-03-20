// SPDX-License-Identifier: Apache-2.0

// FPV monitor for br_cdc_reg

`include "br_asserts.svh"

module br_cdc_reg_fpv_monitor #(
    parameter int Width = 1,  // Must be at least 1
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterResetActive = 1,
    parameter int NumSyncStages = 3,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1 use Jasper scoreboard, else use Synopsys FML scoreboard
    parameter bit Jasper = 1
) (

    // FV system clk and rst
    input logic clk,
    input logic rst,

    // Push-side interface.
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic pop_clk,
    input logic pop_rst,
    input logic pop_ready
);
  // ----------Instantiate DUT----------
  logic push_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  br_cdc_reg #(
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) dut (
      .push_clk,
      .push_rst,
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  // ----------Assumptions----------
  if (!EnableCoverPushBackpressure) begin : gen_backpressure
    `BR_ASSUME(no_backpressure_a, !push_ready |-> !push_valid)
  end
  if (EnableAssertPushValidStability) begin : gen_push_valid_stable
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data_stable
    `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data))
  end

  // ----------Data integrity Check----------
  logic push_beat;
  logic pop_beat;

  assign push_beat = push_valid && push_ready;
  assign pop_beat  = pop_valid && pop_ready;

  if (Jasper) begin : gen_jasper
    jasper_scoreboard_3 #(
        .CHUNK_WIDTH(Width),
        .IN_CHUNKS(1),
        .OUT_CHUNKS(1),
        .SINGLE_CLOCK(0),
        .MAX_PENDING(1 + RegisterPopOutputs)
    ) scoreboard (
        .incoming_clk(push_clk),
        .outgoing_clk(pop_clk),
        .rstN(!rst),
        .incoming_vld(push_beat),
        .incoming_data(push_data),
        .outgoing_vld(pop_beat),
        .outgoing_data(pop_data)
    );
  end else begin : gen_snps
    snps_fml_scoreboard #(
        .DATA_CHUNK_WIDTH(Width),
        .NUM_OF_IN_CHUNKS(1),
        .NUM_OF_OUT_CHUNKS(1),
        .MAX_OUTSTANDING_CHUNKS(1 + RegisterPopOutputs),
        .ENABLE_INORDER(1),
        .ENABLE_DUAL_CLOCKS(1),
        .SCBMODE(0)
    ) scoreboard (
        .Resetn(!rst),
        .ClkIn(push_clk),
        .ValidIn(push_beat),
        .DataIn(push_data),
        .ClkOut(pop_clk),
        .ValidOut(pop_beat),
        .DataOut(pop_data)
    );
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(no_deadlock_pop_a, push_beat |-> s_eventually pop_valid)
endmodule : br_cdc_reg_fpv_monitor
