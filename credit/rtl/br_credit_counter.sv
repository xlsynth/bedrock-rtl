// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_counter #(
    // Width of the MaxValue parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxValueWidth = 32,
    // Width of the MaxChange parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxChangeWidth = 32,
    // Maximum credit counter value (inclusive). Must be at least 1.
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    // Maximum increment/decrement amount (inclusive). Must be at least 1.
    parameter logic [MaxChangeWidth-1:0] MaxChange = 1,
    // Maximum increment amount (inclusive). Must be at least 1 and at most MaxChange.
    parameter logic [MaxChangeWidth-1:0] MaxIncrement = MaxChange,
    // Maximum decrement amount (inclusive). Must be at least 1 and at most MaxChange.
    parameter logic [MaxChangeWidth-1:0] MaxDecrement = MaxChange,
    // If 1, cover that you can have incr_valid high with incr = 0.
    // Otherwise, assert that doesn't happen.
    parameter bit EnableCoverZeroIncrement = 1,
    // If 1, cover that you can have decr_valid high with decr = 0.
    // Otherwise, assert that doesn't happen.
    parameter bit EnableCoverZeroDecrement = 1,
    // If 1, cover the case where decr_valid is high and decr_ready is low.
    // Otherwise, assert that doesn't happen.
    parameter bit EnableCoverDecrementBackpressure = 1,
    // If 1, cover that withhold can be non-zero.
    // Otherwise, assert that it is always zero.
    parameter bit EnableCoverWithhold = 1,
    // If 1, assert that decr_valid is always high.
    // Otherwise, cover that it can be low.
    // Generally, this should not be enabled unless decr_valid is tied high.
    parameter bit EnableAssertAlwaysDecr = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // The maximum credit count value that will be checked by covers.
    parameter logic [MaxValueWidth-1:0] CoverMaxValue = MaxValue,
    // If 1, then at the end of simulation, assert that the credit counter value equals
    // the maximum number of credits that it stored at any point during the test.
    // Mutually exclusive with EnableAssertFinalMinValue.
    parameter bit EnableAssertFinalMaxValue = 0,
    // If 1, then at the end of simulation, assert that the credit counter value equals
    // the minimum number of credits that it stored at any point during the test.
    // Mutually exclusive with EnableAssertFinalMaxValue.
    parameter bit EnableAssertFinalMinValue = 0,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxChangeP1Width = MaxChangeWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int ChangeWidth = $clog2(MaxChangeP1Width'(MaxChange) + 1)
) (
    // Posedge-triggered clock.
    input  logic                   clk,
    // Synchronous active-high reset.
    input  logic                   rst,
    // Supports independent increment and decrement on the same cycle.
    input  logic                   incr_valid,
    input  logic [ChangeWidth-1:0] incr,
    output logic                   decr_ready,
    input  logic                   decr_valid,
    input  logic [ChangeWidth-1:0] decr,
    // Reset value for the credit counter
    input  logic [ ValueWidth-1:0] initial_value,
    // Dynamically withhold credits from circulation
    input  logic [ ValueWidth-1:0] withhold,
    // Credit counter state not including increment & withhold.
    output logic [ ValueWidth-1:0] value,
    // Dynamic amount of available credit including increment & withhold.
    output logic [ ValueWidth-1:0] available
);
  //------------------------------------------
  // Integration checks
  //------------------------------------------

  // Parameter checks
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_change_gte_1_a, MaxChange >= 1)
  `BR_ASSERT_STATIC(max_change_lte_max_value_a, MaxChange <= MaxValue)
  `BR_ASSERT_STATIC(legal_max_increment_a, MaxIncrement >= 1 && MaxIncrement <= MaxChange)
  `BR_ASSERT_STATIC(legal_max_decrement_a, MaxDecrement >= 1 && MaxDecrement <= MaxChange)
  `BR_ASSERT_STATIC(cover_max_value_lte_max_value_a, CoverMaxValue <= MaxValue)
  `BR_ASSERT_STATIC(assert_final_value_mutually_exclusive_a,
                    !(EnableAssertFinalMaxValue && EnableAssertFinalMinValue))

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_incr_valid_a, !incr_valid)
    `BR_ASSERT_FINAL(final_not_decr_valid_a, !decr_valid)
  end

  if (EnableAssertAlwaysDecr) begin : gen_assert_always_decr
    `BR_ASSERT_INTG(always_decr_a, decr_valid)
  end else begin : gen_cover_sometimes_no_decr
    `BR_COVER_INTG(no_decr_c, !decr_valid)
  end

  // Ensure increments and decrements are in range
  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> (incr <= MaxIncrement))
  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> (decr <= MaxDecrement))

  // Assertion-only helper logic for overflow/underflow detection
`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  localparam int CalcWidth = ValueWidth + 1;
  logic [CalcWidth-1:0] value_extended_next;

  // Compute the next value with extended width
  // ri lint_check_waive IFDEF_CODE
  always_comb begin
    value_extended_next = {1'b0, value};
    // ri lint_check_waive SEQ_COND_ASSIGNS
    if (incr_valid) value_extended_next = value_extended_next + CalcWidth'(incr);
    // ri lint_check_waive SEQ_COND_ASSIGNS ONE_IF_CASE
    if (decr_valid && decr_ready) value_extended_next = value_extended_next - CalcWidth'(decr);
  end

  if (EnableAssertFinalMaxValue) begin : gen_assert_final_max_value
    logic [ValueWidth-1:0] max_credit_value, max_credit_value_next;
    `BR_REG(max_credit_value, max_credit_value_next)
    assign max_credit_value_next = value > max_credit_value ? value : max_credit_value;
    `BR_ASSERT_FINAL(final_max_value_a, value == max_credit_value)
  end
  if (EnableAssertFinalMinValue) begin : gen_assert_final_min_value
    logic [ValueWidth-1:0] min_credit_value, min_credit_value_next;
    `BR_REGI(min_credit_value, min_credit_value_next, initial_value)
    assign min_credit_value_next = value < min_credit_value ? value : min_credit_value;
    `BR_ASSERT_FINAL(final_min_value_a, value == min_credit_value)
  end

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  `BR_ASSERT_INTG(no_overflow_or_underflow_a, value_extended_next <= MaxValue)

  // Ensure the credit counter goes through the full range to help ensure
  // flow control corners are hit outside the module.
  `BR_COVER_INTG(value_reaches_zero_c, value == 0)
  `BR_COVER_INTG(value_reaches_max_c, value == CoverMaxValue)

  // Ensure the initial value was within the valid range on the last cycle when exiting reset
  `BR_ASSERT_INTG(initial_value_in_range_a, $fell(rst) |-> $past(initial_value) <= MaxValue)

  // Withhold and available
  `BR_ASSERT_INTG(withhold_in_range_a, withhold <= MaxValue)
  if (EnableCoverWithhold) begin : gen_cover_withhold_nonzero
    `BR_COVER_INTG(withhold_nonzero_c, withhold > 0)
  end else begin : gen_assert_withhold_zero
    `BR_ASSERT_INTG(withhold_zero_a, withhold == 0)
  end

  if (EnableCoverDecrementBackpressure) begin : gen_cover_decr_gt_available
    `BR_COVER_INTG(decr_gt_available_c, decr_valid && decr > available)
  end else begin : gen_assert_decr_lte_available
    `BR_ASSERT_INTG(decr_lte_available_a, decr_valid |-> decr <= available)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Counter
  logic [ChangeWidth-1:0] incr_internal;
  logic [ChangeWidth-1:0] decr_internal;
  logic [ ValueWidth-1:0] value_plus_incr;
  logic [ ValueWidth-1:0] value_next;
  logic                   value_loaden;

  // ri lint_check_waive CONST_ASSIGN
  assign incr_internal = incr_valid ? incr : '0;
  // ri lint_check_waive CONST_ASSIGN
  assign decr_internal = decr_valid ? decr : '0;
  assign value_plus_incr = value + ValueWidth'(incr_internal);
  assign value_next = value_plus_incr - (decr_ready ? ValueWidth'(decr_internal) : '0);
  assign value_loaden = incr_valid || (decr_valid && decr_ready);

  `BR_REGLI(value, value_next, value_loaden, initial_value)

  // Withhold and available: don't use the decrement in the calculation of
  // available credits because that would cause a combinational loop
  assign available = value_plus_incr > withhold ? value_plus_incr - withhold : '0;

  if (MaxDecrement == 1) begin : gen_decr_ready_one
    assign decr_ready = available > '0;
  end else begin : gen_decr_ready_gt_one
    assign decr_ready = ValueWidth'(decr_internal) <= available;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Reset
  `BR_ASSERT_IMPL(reset_behavior_a, $fell(rst) |-> value == $past(initial_value))

  // Value basics
  `BR_ASSERT_IMPL(value_next_a, value_next == value_extended_next[ValueWidth-1:0])
  `BR_ASSERT_IMPL(value_updates_a, ##1 !$fell(rst) |-> value == $past(value_next))

  // Increment corners
  `BR_COVER_IMPL(max_incr_c, incr_valid && incr == MaxIncrement)
  if (EnableCoverZeroIncrement) begin : gen_cover_zero_increment
    `BR_COVER_IMPL(min_incr_c, incr_valid && incr == '0)
  end else begin : gen_assert_nonzero_increment
    `BR_ASSERT_IMPL(nonzero_incr_a, incr_valid |-> incr != '0)
  end

  // Decrement corners
  `BR_COVER_IMPL(max_decr_c, decr_valid && decr == MaxDecrement)
  if (EnableCoverZeroDecrement) begin : gen_cover_zero_decrement
    `BR_COVER_IMPL(min_decr_c, decr_valid && decr == '0)
  end else begin : gen_assert_nonzero_decrement
    `BR_ASSERT_IMPL(nonzero_decr_a, decr_valid |-> decr != '0)
  end

  // Increment/decrement combination corner cases
  `BR_COVER_IMPL(incr_and_decr_c, incr_valid && decr_valid)
  if (!EnableAssertAlwaysDecr) begin : gen_assert_incr_and_no_decr
    `BR_ASSERT_IMPL(incr_and_no_decr_c, incr_valid && !decr_valid |-> value_next >= value)
  end
  `BR_ASSERT_IMPL(no_incr_and_decr_c, !incr_valid && decr_valid |-> value_next <= value)

  // No-op corners
  if (!EnableAssertAlwaysDecr) begin : gen_assert_idle_noop
    `BR_ASSERT_IMPL(idle_noop_a, !incr_valid && !decr_valid |-> value == value_next)
  end
  `BR_ASSERT_IMPL(active_noop_a,
                  incr_valid && decr_valid && decr_ready && incr == decr |-> value == value_next)

  // Withhold and available
  `BR_COVER_IMPL(value_lt_available_c, value < available)
  if (EnableCoverWithhold) begin : gen_cover_withhold_gt_value
    `BR_COVER_IMPL(value_gt_available_c, value > available)
    `BR_COVER_IMPL(withhold_gt_value_c, withhold > value)
  end

endmodule : br_credit_counter
