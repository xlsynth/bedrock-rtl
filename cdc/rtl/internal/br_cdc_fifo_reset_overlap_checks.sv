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

  logic overlap_next, counter_rst, reset_active_push_d, reset_active_pop_d;
  logic [CounterWidth-1:0] overlap_cycles, overlap_cycles_next;

  `BR_REGN(reset_active_push_d, reset_active_push)
  `BR_REGN(reset_active_pop_d, reset_active_pop)

  assign overlap_next = reset_active_push === 1'b1 && reset_active_pop === 1'b1;

  // Reset the overlap counter on the rising edge of either reset, when both resets are known.
  // ri lint_check_waive FOURSTATE_COMP X_USE
  assign counter_rst = (reset_active_push !== 1'bx && reset_active_pop !== 1'bx) &&
      // ri lint_check_waive FOURSTATE_COMP
      ((reset_active_push === 1'b1 && reset_active_push_d !== 1'b1) ||
      // ri lint_check_waive FOURSTATE_COMP
      (reset_active_pop === 1'b1 && reset_active_pop_d !== 1'b1));

  // Not using br_counter_incr because it has implementation assertions
  // that assume we won't drive Xes into its inputs when it's not in reset.
  `BR_REGN(overlap_cycles, overlap_cycles_next)
  always_comb begin
    overlap_cycles_next = overlap_cycles;
    // Lint bug? Says counter_rst is constant false (but that's not the case in VCS waves).
    // ri lint_check_waive CONST_IF_COND
    if (counter_rst) begin
      if (overlap_next) begin
        overlap_cycles_next = CounterWidth'(1'b1);
      end else begin
        overlap_cycles_next = '0;
      end
    end else if (overlap_next) begin
      overlap_cycles_next = overlap_cycles + 1;
    end
  end

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  `BR_ASSERT_CR_INTG(reset_overlap_a, $fell(reset_active_push) || $fell(reset_active_pop)
                                      |-> overlap_cycles >= MinOverlapCycles, clk, 1'b0)

endmodule : br_cdc_fifo_reset_overlap_checks
