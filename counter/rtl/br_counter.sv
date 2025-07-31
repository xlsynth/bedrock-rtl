// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL Increment/Decrement Counter w/ Overflow Handling
//
// A simple counter that increments and/or decrements by a potentially variable
// amount each cycle, where the maximum change is given by MaxChange
// (inclusive).
//
// Overflows (wraps around past 0) at MaxValue (inclusive), and Underflows up
// to MaxValue even if MaxValue + 1 isn't a power-of-2. In the common case
// where MaxValue + 1 is a power-of-2, the implementation is simplified.
//
// The counter state is exposed in two ways.
// (1) value holds the current counter state. There is a latency of 1 cycle from
//     a valid change to the counter state being updated.
// (2) value_next is what value will be on the next cycle. It is conditioned on
//     incr_valid and decr_valid: if both are low, then value_next == value.
//     This is useful for constructing single-cycle chains of counters.
// value and value_next are always valid.
//
// The counter value resets to initial_value.
//
// The reinit port reinitializes the counter to initial_value.
// This does *nearly* the same thing as rst but is likely to be driven by completely different
// logic. Rather than having the user mix together an expression involving both rst and reinit,
// a separate port helps keep the user's reset code clean and correct. Also, unlike reset, the
// reinit can accommodate a change on the same cycle, i.e., the change
// applies to the initial value rather than the old value.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_counter #(
    // Width of the MaxValue parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxValueWidth = 32,
    // Width of the MaxChange parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxChangeWidth = 32,
    // Must be at least 1. Inclusive.
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    // Must be at least 1 and at most MaxValue. Inclusive.
    parameter logic [MaxChangeWidth-1:0] MaxChange = 1,
    // The actual maximum increment value. Must be >=1 and <=MaxValue.
    parameter logic [MaxChangeWidth-1:0] MaxIncrement = MaxChange,
    // The actual maximum decrement value. Must be >=1 and <=MaxValue.
    parameter logic [MaxChangeWidth-1:0] MaxDecrement = MaxChange,
    // If 1, allow the counter value to wrap around 0/MaxValue, adding additional correction
    // logic to do so if MaxValue is not 1 less than a power of two.
    // If 0, don't allow wrapping and omit overflow/underflow correction logic.
    // Assert there is no overflow/underflow.
    // Must be 0 if EnableSaturate is 1.
    parameter bit EnableWrap = 1,
    // If 1, then when reinit is asserted together with incr_valid and/or decr_valid,
    // the increment/decrement are applied to the initial value rather than the current value, i.e.,
    // value_next == initial_value + applicable incr - applicable decr.
    // If 0, then when reinit is asserted together with incr_valid and/or decr_valid,
    // the increment/decrement values are ignored, i.e., value_next == initial_value.
    parameter bit EnableReinitAndChange = 1,
    // If 1, the counter value saturates at 0 and MaxValue.
    // If 0, the counter value wraps around at 0 and MaxValue.
    // Must be 0 if EnableWrap is 1.
    parameter bit EnableSaturate = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, cover the case where incr_valid or decr_valid is 1, but
    // incr or decr is 0, respectively.
    // Otherwise, assert that incr and decr are always non-zero when incr_valid or decr_valid is 1.
    parameter bit EnableCoverZeroChange = 1,
    // If 1, enable reinit-related coverage.
    // If 0, assert that reinit is never asserted.
    parameter bit EnableCoverReinit = 1,
    // If 1, cover the cases where reinit is asserted together with incr_valid and/or decr_valid.
    // Otherwise, assert that reinit is only asserted when incr_valid and decr_valid are both 0.
    parameter bit EnableCoverReinitAndChange = EnableCoverReinit,
    // If 1, cover the case where reinit is asserted when incr_valid and decr_valid are both 0.
    // Otherwise, assert that reinit is never asserted when incr_valid and decr_valid are both 0.
    parameter bit EnableCoverReinitNoChange = EnableCoverReinit,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxChangeP1Width = MaxChangeWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int ChangeWidth = $clog2(MaxChangeP1Width'(MaxChange) + 1)
) (
    // Posedge-triggered clock.
    input  logic                   clk,
    // Synchronous active-high reset.
    input  logic                   rst,
    input  logic                   reinit,
    input  logic [ ValueWidth-1:0] initial_value,
    input  logic                   incr_valid,
    input  logic [ChangeWidth-1:0] incr,
    input  logic                   decr_valid,
    input  logic [ChangeWidth-1:0] decr,
    output logic [ ValueWidth-1:0] value,
    output logic [ ValueWidth-1:0] value_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(value_width_gte_1_a, ValueWidth >= 1)
  `BR_ASSERT_STATIC(change_width_gte_1_a, ChangeWidth >= 1)
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_change_gte_1_a, MaxChange >= 1)
  `BR_ASSERT_STATIC(max_change_lte_max_value_a, MaxChange <= MaxValue)
  `BR_ASSERT_STATIC(max_increment_gte_1_a, MaxIncrement >= 1)
  `BR_ASSERT_STATIC(max_increment_lte_max_change_a, MaxIncrement <= MaxChange)
  `BR_ASSERT_STATIC(max_decrement_gte_1_a, MaxDecrement >= 1)
  `BR_ASSERT_STATIC(max_decrement_lte_max_change_a, MaxDecrement <= MaxChange)
  `BR_ASSERT_STATIC(no_wrap_and_saturate_a, !(EnableWrap && EnableSaturate))

  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> incr <= MaxIncrement)
  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> decr <= MaxDecrement)
  `BR_ASSERT_INTG(initial_value_in_range_a, initial_value <= MaxValue)

  // Assertion-only helper logic for overflow/underflow detection
`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  localparam int ExtWidth = $clog2(MaxValue + MaxChange + 1);
  logic [ExtWidth-1:0] value_extended;
  logic [ExtWidth-1:0] value_extended_next;

  // ri lint_check_waive IFDEF_CODE
  assign value_extended = ExtWidth'(value);
  // ri lint_check_waive IFDEF_CODE
  assign value_extended_next =
      // ri lint_check_waive ARITH_ARGS
      value_extended + (incr_valid ? incr : '0) - (decr_valid ? decr : '0);

  if (EnableWrap || EnableSaturate) begin : gen_wrap_or_saturate_cover
    `BR_COVER_INTG(wrap_or_saturate_c, value_extended_next > MaxValue)
  end else begin : gen_no_wrap_or_saturate_assert
    `BR_ASSERT_INTG(no_wrap_or_saturate_a, value_extended_next <= MaxValue)
  end
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_incr_valid_a, !incr_valid)
    `BR_ASSERT_FINAL(final_not_decr_valid_a, !decr_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam logic [MaxValueP1Width-1:0] MaxValueP1 = MaxValue + 1;
  localparam bit IsMaxValueP1PowerOf2 = (MaxValueP1 & (MaxValueP1 - 1)) == 0;
  localparam int TempWidth = $clog2(MaxValueP1Width'(MaxValue) + MaxChangeP1Width'(MaxChange) + 1);
  localparam logic [ValueWidth-1:0] MaxValueResized = ValueWidth'(MaxValue);
  localparam logic [TempWidth-1:0] MaxValueWithOverflow = TempWidth'(MaxValue);

  logic                   value_loaden;
  // The MSB might not be used
  // ri lint_check_waive INEFFECTIVE_NET
  logic [  TempWidth-1:0] value_temp;
  logic [ChangeWidth-1:0] incr_qual;
  logic [ChangeWidth-1:0] decr_qual;

  assign incr_qual = incr_valid ? incr : '0;
  assign decr_qual = decr_valid ? decr : '0;

  if (EnableReinitAndChange) begin : gen_reinit_and_change
    // ri lint_check_waive ARITH_ARGS RHS_TOO_SHORT ARITH_BITLEN
    assign value_temp = (reinit ? initial_value : value) + incr_qual - decr_qual;
  end else begin : gen_reinit_ignore_change
    // ri lint_check_waive ARITH_ARGS RHS_TOO_SHORT ARITH_BITLEN
    assign value_temp = reinit ? initial_value : (value + incr_qual - decr_qual);
  end
  assign value_loaden = reinit || incr_valid || decr_valid;

  // For MaxValueP1 being a power of 2, wrapping occurs naturally
  if (!EnableSaturate && (IsMaxValueP1PowerOf2 || !EnableWrap)) begin : gen_no_wrap_or_saturate
    assign value_next = value_temp[ValueWidth-1:0];  // ri lint_check_waive FULL_RANGE

    if (TempWidth > ValueWidth) begin : gen_unused
      `BR_UNUSED_NAMED(value_temp_msbs, value_temp[TempWidth-1:ValueWidth])
    end
    // For MaxValueP1 not being a power of 2, handle wrap-around explicitly
  end else begin : gen_wrap_or_saturate
    logic is_net_decr;
    logic would_out_of_bounds;
    logic would_underflow;
    logic would_overflow;

    assign is_net_decr = decr_qual > incr_qual;
    assign would_out_of_bounds = value_temp > MaxValueWithOverflow;
    assign would_underflow = would_out_of_bounds && is_net_decr;
    assign would_overflow = would_out_of_bounds && !is_net_decr;

    if (EnableSaturate) begin : gen_saturate
      logic [ValueWidth-1:0] value_next_saturated;

      assign value_next_saturated = MaxValueResized;
      assign value_next = would_underflow ? '0 :
                          would_overflow ? value_next_saturated :
                          value_temp[ValueWidth-1:0];

      if (TempWidth > ValueWidth) begin : gen_unused
        `BR_UNUSED_NAMED(value_temp_msbs, value_temp[TempWidth-1:ValueWidth])
      end
    end else begin : gen_wrap
      // The MSB will not be used
      // ri lint_check_waive INEFFECTIVE_NET
      logic [TempWidth-1:0] max_value_p1;
      logic [TempWidth-1:0] value_temp_wrapped;

      assign max_value_p1 = TempWidth'(MaxValueP1);
      assign value_temp_wrapped =
          would_underflow ? (value_temp + max_value_p1) :
          would_overflow  ? (value_temp - max_value_p1) :
                          value_temp;
      // If TempWidth == ValueWidth, the bit select covers the full range
      // ri lint_check_waive FULL_RANGE
      assign value_next = value_temp_wrapped[ValueWidth-1:0];

      if (TempWidth > ValueWidth) begin : gen_unused
        `BR_UNUSED_NAMED(value_temp_wrapped_msbs, value_temp_wrapped[TempWidth-1:ValueWidth])
      end
    end
  end

  `BR_REGLI(value, value_next, value_loaden, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(value_in_range_a, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_a, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_a, ##1 !$past(rst) |-> value == $past(value_next))

  // Change corners
  `BR_COVER_IMPL(increment_max_c, incr_valid && incr == MaxIncrement)
  `BR_COVER_IMPL(decrement_max_c, decr_valid && decr == MaxDecrement)
  if (EnableCoverZeroChange) begin : gen_cover_zero_change
    `BR_COVER_IMPL(increment_zero_c, incr_valid && incr == '0)
    `BR_COVER_IMPL(decrement_zero_c, decr_valid && decr == '0)
  end else begin : gen_assert_no_zero_change
    `BR_ASSERT_IMPL(no_zero_increment_a, !incr_valid |-> incr > '0)
    `BR_ASSERT_IMPL(no_zero_decrement_a, !decr_valid |-> decr > '0)
  end
  `BR_COVER_IMPL(increment_and_decrement_c, incr_valid && incr > '0 && decr_valid && decr > '0)

  // Reinit
  if (EnableCoverReinit) begin : gen_cover_reinit
    if (EnableCoverReinitAndChange) begin : gen_cover_reinit_and_change
      `BR_COVER_IMPL(reinit_and_change_c, reinit && (incr_valid || decr_valid))
    end else begin : gen_assert_no_change_on_reinit
      `BR_ASSERT_IMPL(no_change_on_reinit_a, reinit |-> !incr_valid && !decr_valid)
    end

    if (EnableCoverReinitNoChange) begin : gen_cover_reinit_no_change
      `BR_ASSERT_IMPL(reinit_no_change_a,
                      reinit && !incr_valid && !decr_valid |=> value == $past(initial_value))
    end else begin : gen_assert_no_reinit_without_change
      `BR_ASSERT_IMPL(no_reinit_without_change_a, reinit |-> (incr_valid || decr_valid))
    end
  end else begin : gen_assert_no_reinit
    `BR_ASSERT_IMPL(no_reinit_a, !reinit)
  end

endmodule : br_counter
