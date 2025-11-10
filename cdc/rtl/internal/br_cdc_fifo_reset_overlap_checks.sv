// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_registers.svh"

// Integration assertion-only module that checks the push and pop-clock domain
// resets of a CDC FIFO overlap for each a minimum number of cycles within a
// given clock domain.
//
// The CDC FIFO is not a reset domain crossing, so this checker is necessary to
// ensure that both sides of the FIFO are held in reset at the same time.

// ri lint_check_waive NO_OUTPUT
module br_cdc_fifo_reset_overlap_checks #(
    // The minimum number of cycles that the two resets must overlap high.
    // Must be at least 1.
    // ri lint_check_waive PARAM_NOT_USED
    parameter int MinOverlapCycles = 1
) (
    // Either the push clk or the pop clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic clk,
    // Reset that originates from the push clock domain. Must be synchronous to clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic reset_active_push,
    // Reset that originates from the pop clock domain. Must be synchronous to clk.
    // ri lint_check_waive INPUT_NOT_READ
    input logic reset_active_pop
);

  `BR_ASSERT_STATIC(legal_min_overlap_cycles_a, MinOverlapCycles >= 1)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS

`ifdef SYNTHESIS
  // We have to be extra careful not to try to synthesize these checks.
  // We do funky things like 4-state comparisons.
  `BR_ASSERT_STATIC(do_not_synthesize_reset_overlap_checks_a, 0)
`endif  // SYNTHESIS

  localparam int MaxValue = 1 << 31;
  localparam int CounterWidth = $clog2(MaxValue + 1);

  logic overlap, overlap_next, counter_rst;
  logic [CounterWidth-1:0] overlap_cycles, overlap_cycles_next;

  `BR_REGN(overlap, overlap_next)
  assign overlap_next = reset_active_push && reset_active_pop;
  // ri lint_check_waive FOURSTATE_COMP
  assign counter_rst = (reset_active_push === 1'b1 && reset_active_pop !== 1'b1) ||
      // ri lint_check_waive FOURSTATE_COMP
      (reset_active_push !== 1'b1 && reset_active_pop === 1'b1);

  // Not using br_counter_incr because it has implementation assertions
  // that assume we won't drive Xes into its inputs when it's not in reset.
  `BR_REGLX(overlap_cycles, overlap_cycles_next, overlap_next, clk, counter_rst)
  assign overlap_cycles_next = overlap_cycles + 1'b1;

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  `BR_ASSERT_CR_INTG(reset_overlap_a,
                     overlap && !overlap_next |-> overlap_cycles >= MinOverlapCycles, clk, 1'b0)

endmodule : br_cdc_fifo_reset_overlap_checks
