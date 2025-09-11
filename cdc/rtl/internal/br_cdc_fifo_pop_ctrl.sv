// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_cdc_fifo_pop_ctrl #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int RamReadLatency = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterResetActive = 1,
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

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Pop-side status flags
    output logic                  empty,
    output logic [CountWidth-1:0] items,

    // RAM interface
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    // Not used except for assertions in some configurations.
    // ri lint_check_waive INEFFECTIVE_NET
    input  logic                 ram_rd_data_valid,
    input  logic [    Width-1:0] ram_rd_data,

    // Signals synchronized from/to the push side
    input  logic [CountWidth-1:0] push_count_gray,
    output logic [CountWidth-1:0] pop_count_gray,
    input  logic                  reset_active_push,
    output logic                  reset_active_pop
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  `BR_ASSERT_INTG(ram_rd_latency_matches_a,
                  ram_rd_addr_valid |-> ##RamReadLatency ram_rd_data_valid)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Core flow-control logic

  logic pop_beat;

  br_fifo_pop_ctrl_core #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(1'b0),  // Bypass is not used for CDC
      .RamReadLatency(RamReadLatency),
      .RegisterPopOutputs(RegisterPopOutputs),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_pop_ctrl_core (
      .clk,
      .rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .bypass_ready(),  // Not used
      .bypass_valid_unstable(1'b0),  // Not used
      .bypass_data_unstable(Width'(1'b0)),  // Not used
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data,
      .empty,
      .items,
      .pop_beat
  );

  // Status flags
  br_cdc_fifo_pop_flag_mgr #(
      .Depth(Depth),
      .RegisterResetActive(RegisterResetActive),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_pop_flag_mgr (
      .clk,
      .rst,
      .pop_beat,
      .push_count_gray,
      .pop_count_gray,
      .items,
      .empty,
      .reset_active_push,
      .reset_active_pop
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(ram_rd_addr_in_range_a, ram_rd_addr_valid |-> ram_rd_addr < Depth)

  // Flow control
  `BR_ASSERT_IMPL(no_pop_valid_on_empty_a, pop_valid |-> !empty)

  // Flags
  `BR_ASSERT_IMPL(items_in_range_a, items <= Depth)
  `BR_ASSERT_IMPL(empty_a, empty == (items == 0))

endmodule : br_cdc_fifo_pop_ctrl
