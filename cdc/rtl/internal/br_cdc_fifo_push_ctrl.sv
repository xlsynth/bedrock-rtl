// SPDX-License-Identifier: Apache-2.0

//
// Push Controller for CDC FIFO with Ready/Valid interface

`include "br_asserts_internal.svh"

module br_cdc_fifo_push_ctrl #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int RamWriteLatency = 1,
    parameter bit RegisterResetActive = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = 1,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  full,
    output logic [CountWidth-1:0] slots,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,

    // Signals to/from pop controller
    input  logic [CountWidth-1:0] pop_count_gray,
    output logic [CountWidth-1:0] push_count_gray,
    input  logic                  reset_active_pop,
    output logic                  reset_active_push
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_COVER_INTG(full_c, full)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic push_beat;

  br_cdc_fifo_push_flag_mgr #(
      .Depth(Depth),
      .RamWriteLatency(RamWriteLatency),
      .RegisterResetActive(RegisterResetActive),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_push_flag_mgr (
      .clk,
      .rst,
      .push_beat,
      .push_count_gray,
      .pop_count_gray,
      .pop_count_delta(),
      .slots,
      .full,
      .reset_active_push,
      .reset_active_pop
  );

  // Core flow-control logic
  logic [AddrWidth-1:0] addr_base;
  logic [AddrWidth-1:0] addr_bound;

  assign addr_base  = '0;
  assign addr_bound = Depth - 1;

  br_fifo_push_ctrl_core #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(1'b0),  // Bypass is not enabled for CDC
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_push_ctrl_core (
      .clk,
      .rst,

      .addr_base,
      .addr_bound,

      .push_ready,
      .push_valid,
      .push_data,

      .bypass_ready(1'b0),  // Bypass not used
      .bypass_valid_unstable(),  // Bypass not used
      .bypass_data_unstable(),  // Bypass not used

      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_addr_next(),
      .ram_wr_data,

      .full,
      .push_beat
  );

  // Implementation checks
  // Implementation checks
  `BR_ASSERT_IMPL(ram_wr_addr_in_range_a, ram_wr_valid |-> ram_wr_addr < Depth)

  // Flow control and latency
  `BR_ASSERT_IMPL(push_backpressure_when_full_a, full |-> !push_ready)

  // Flags
  `BR_ASSERT_IMPL(slots_in_range_a, slots <= Depth)
  `BR_ASSERT_IMPL(full_a, full == (slots == 0))

endmodule : br_cdc_fifo_push_ctrl
