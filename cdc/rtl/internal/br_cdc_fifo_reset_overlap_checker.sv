// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_registers.svh"

// Integration assertion-only module that checks the push and pop-clock domain
// resets of a CDC FIFO overlap for each a minimum number of cycles within a
// given clock domain.

// ri lint_check_waive NO_OUTPUT
module br_cdc_fifo_reset_overlap_checker #(
    // The minimum number of cycles that the two resets must overlap high.
    // Must be at least 1.
    // ri lint_check_waive PARAM_NOT_USED
    parameter int MinOverlapCycles = 1,
    // ri lint_check_waive PARAM_NOT_USED
    localparam int CounterWidth = $clog2(MinOverlapCycles + 1)
) (
    // Either the push clk or the pop clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic clk,
    // Reset that originates from the push clock domain. Must be synchronous to clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic push_rst_active,
    // Reset that originates from the pop clock domain. Must be synchronous to clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic pop_rst_active
);

  `BR_ASSERT_STATIC(legal_min_overlap_cycles_a, MinOverlapCycles >= 1)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS

  logic overlap, overlap_next;
  logic [CounterWidth-1:0] overlap_cycles;

  `BR_REGN(overlap, overlap_next)
  assign overlap_next = push_rst_active && pop_rst_active;

  br_counter_incr #(
      .MaxValue(MinOverlapCycles),
      .EnableAssertFinalNotValid(0),
      .EnableCoverZeroIncrement(0),
      .EnableCoverReinit(0)
  ) br_counter_incr_overlap (
      .clk,
      .rst(1'b0),
      .reinit(!overlap_next),
      .initial_value('0),
      .incr_valid(overlap_next),
      .incr(1'b1),
      .value(overlap_cycles),
      .value_next()
  );

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  `BR_ASSERT_CR_INTG(reset_overlap_a,
                     overlap && !overlap_next |-> overlap_cycles >= MinOverlapCycles, clk, 1'b0)

endmodule : br_cdc_fifo_reset_overlap_checker
