// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_cdc_fifo_ctrl_push_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // The number of push cycles after ram_wr_valid is asserted at which
    // it is safe to read the newly written data.
    parameter int RamWriteLatency = 1,
    // The number of synchronization stages to use for the gray counts.
    parameter int NumSyncStages = 3,
    // If 1 (the default), register push_rst on push_clk before sending it out
    // as push_reset_active_push. This adds an extra cycle to the cut-through
    // latency of the FIFO.
    // Do not set this to 0 unless either push_rst is driven directly by a
    // register or if push_reset_active_push is registered externally
    // before synchronization to the pop clock domain.
    parameter bit RegisterResetActive = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Push-side interface
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  push_full,
    output logic [CountWidth-1:0] push_slots,

    // Push-side RAM write interface
    output logic                 push_ram_wr_valid,
    output logic [AddrWidth-1:0] push_ram_wr_addr,
    output logic [    Width-1:0] push_ram_wr_data,

    // Posedge-triggered clock.
    input logic pop_clk,
    // Synchronous active-high reset.
    input logic pop_rst,

    // Signals that connect to the pop side.
    input  logic                  pop_reset_active_pop,
    input  logic [CountWidth-1:0] pop_pop_count_gray,
    output logic [CountWidth-1:0] push_push_count_gray,
    output logic                  push_reset_active_push
);
  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [CountWidth-1:0] push_pop_count_gray;
  logic                  push_reset_active_pop;

  br_cdc_fifo_push_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .RamWriteLatency(RamWriteLatency),
      .RegisterResetActive(RegisterResetActive),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_push_ctrl (
      .clk              (push_clk),               // ri lint_check_waive SAME_CLOCK_NAME
      .rst              (push_rst),
      .push_ready,
      .push_valid,
      .push_data,
      .full             (push_full),
      .slots            (push_slots),
      .ram_wr_valid     (push_ram_wr_valid),
      .ram_wr_addr      (push_ram_wr_addr),
      .ram_wr_data      (push_ram_wr_data),
      .push_count_gray  (push_push_count_gray),
      .pop_count_gray   (push_pop_count_gray),
      .reset_active_pop (push_reset_active_pop),
      .reset_active_push(push_reset_active_push)
  );

  br_cdc_fifo_gray_count_sync #(
      .CountWidth(CountWidth),
      .NumStages (NumSyncStages)
  ) br_cdc_fifo_gray_count_sync_pop2push (
      // TODO(zhemao): Remove need for pop_clk and pop_rst here.
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_count_gray(pop_pop_count_gray),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_rst),
      .dst_count_gray(push_pop_count_gray)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_reset_active_pop (
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_bit(pop_reset_active_pop),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_rst),
      .dst_bit(push_reset_active_pop)
  );


  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Check that the FIFO backpressures when it is full.
  `BR_ASSERT_CR_IMPL(push_backpressure_when_full_a, push_full |-> !push_ready, push_clk, push_rst)

endmodule : br_cdc_fifo_ctrl_push_1r1w
