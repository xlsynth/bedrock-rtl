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

// Bedrock-RTL Incrementing Counter
//
// A simple counter that increments by a potentially variable amount each cycle,
// where the maximum increment is given by MaxIncrement (inclusive).
// Overflows (wraps around past 0) at MaxValue (inclusive), even if MaxValue + 1
// isn't a power-of-2. In the common case where MaxValue + 1 is a power-of-2,
// the implementation is simplified.
//
// When there is a valid increment and it overflows:
//   value_next = (value + incr) % (MaxValue + 1)
//
// The counter state is exposed in two ways.
// (1) value holds the current counter state. There is a latency of 1 cycle from
//     a valid increment to the counter state being updated.
// (2) value_next is what value will be on the next cycle. It is conditioned on
//     incr_valid: if low, then value_next == value. This is useful for constructing
//     single-cycle chains of counters.
// value and value_next are always valid.
//
// The counter value resets to initial_value.
//
// The reinit port reinitializes the counter to initial_value.
// This does *nearly* the same thing as rst but is likely to be driven by completely different
// logic. Rather than having the user mix together an expression involving both rst and reinit,
// a separate port helps keep the user's reset code clean and correct. Also, unlike reset, the
// reinit can accommodate an increment on the same cycle, i.e., the increment
// applies to the initial value rather than the old value.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_counter_incr #(
    // Width of the MaxValue parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxValueWidth = 32,
    // Width of the MaxIncrement parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    parameter int MaxIncrementWidth = 32,
    // Must be at least 1. Inclusive.
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    // Must be at least 1 and at most MaxValue. Inclusive.
    parameter logic [MaxIncrementWidth-1:0] MaxIncrement = 1,
    // If 1, then when reinit is asserted together with incr_valid,
    // the increment is applied to the initial value rather than the current value, i.e.,
    // value_next == initial_value + applicable incr.
    // If 0, then when reinit is asserted together with incr_valid,
    // the increment values are ignored, i.e., value_next == initial_value.
    parameter bit EnableReinitAndIncr = 1,
    // If 1, the counter value saturates at MaxValue.
    // If 0, the counter value wraps around at MaxValue.
    parameter bit EnableSaturate = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxIncrementP1Width = MaxIncrementWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int IncrementWidth = $clog2(MaxIncrementP1Width'(MaxIncrement) + 1)
) (
    // Posedge-triggered clock.
    input  logic                      clk,
    // Synchronous active-high reset.
    input  logic                      rst,
    input  logic                      reinit,
    input  logic [    ValueWidth-1:0] initial_value,
    input  logic                      incr_valid,
    input  logic [IncrementWidth-1:0] incr,
    output logic [    ValueWidth-1:0] value,
    output logic [    ValueWidth-1:0] value_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(max_value_width_gte_1_a, MaxValueWidth >= 1)
  `BR_ASSERT_STATIC(max_increment_width_gte_1_a, MaxIncrementWidth >= 1)
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_increment_gte_1_a, MaxIncrement >= 1)
  `BR_ASSERT_STATIC(max_increment_lte_max_value_a, MaxIncrement <= MaxValue)

  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> incr <= MaxIncrement)
  `BR_ASSERT_INTG(initial_value_in_range_a, initial_value <= MaxValue)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_incr_valid_a, !incr_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam logic [MaxValueP1Width-1:0] MaxValueP1 = MaxValue + 1;
  localparam bit IsMaxValueP1PowerOf2 = (MaxValueP1 & (MaxValueP1 - 1)) == 0;
  localparam int TempWidth = $clog2(
      MaxValueP1Width'(MaxValue) + MaxIncrementP1Width'(MaxIncrement) + 1
  );
  localparam logic [ValueWidth-1:0] MaxValueResized = ValueWidth'(MaxValue);
  localparam logic [TempWidth-1:0] MaxValueWithOverflow = TempWidth'(MaxValue);

  // TODO(mgottscho): Sometimes the MSbs may not be used. It'd be cleaner
  // to capture them more tightly using br_misc_unused.
  // ri lint_check_waive NOT_READ
  logic [TempWidth-1:0] value_temp;
  if (EnableReinitAndIncr) begin : gen_reinit_and_incr
    // ri lint_check_waive RHS_TOO_SHORT
    assign value_temp = (reinit ? initial_value : value) + (incr_valid ? incr : '0);
  end else begin : gen_reinit_ignore_incr
    // ri lint_check_waive RHS_TOO_SHORT
    assign value_temp = reinit ? initial_value : (value + (incr_valid ? incr : '0));
  end

  if (EnableSaturate) begin : gen_saturate
    logic [ValueWidth-1:0] value_next_saturated;

    assign value_next_saturated = MaxValueResized;
    assign value_next = (value_temp > MaxValueWithOverflow) ?
        value_next_saturated : value_temp[ValueWidth-1:0];

    // For MaxValueP1 being a power of 2, wrapping occurs naturally
  end else if (IsMaxValueP1PowerOf2) begin : gen_power_of_2_wrap
    assign value_next = value_temp[ValueWidth-1:0];

    // For MaxValueP1 not being a power of 2, handle wrap-around explicitly
  end else begin : gen_non_power_of_2_wrap
    // MSBs won't impact outputs if TempWidth > ValueWidth
    // ri lint_check_waive INEFFECTIVE_NET
    logic [TempWidth-1:0] value_temp_wrapped;

    // ri lint_check_waive ARITH_EXTENSION
    assign value_temp_wrapped = (value_temp - MaxValueWithOverflow) - 1;
    // ri lint_check_waive ARITH_EXTENSION
    assign value_next = (value_temp > MaxValueWithOverflow) ?
        value_temp_wrapped[ValueWidth-1:0] :  // ri lint_check_waive FULL_RANGE
        value_temp[ValueWidth-1:0];  // ri lint_check_waive FULL_RANGE

    if (TempWidth > ValueWidth) begin : gen_unused
      `BR_UNUSED_NAMED(value_temp_wrapped_msbs, value_temp_wrapped[TempWidth-1:ValueWidth])
    end
  end

  `BR_REGLI(value, value_next, incr_valid || reinit, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(value_in_range_a, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_a, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_a, ##1 !$past(rst) |-> value == $past(value_next))

  // Overflow corners
  if (EnableSaturate) begin : gen_saturate_impl_check
    `BR_ASSERT_IMPL(value_saturate_a,
                    (incr_valid && value_temp > MaxValue) |-> (value_next == MaxValue))
  end else begin : gen_wrap_impl_check
    `BR_ASSERT_IMPL(
        value_overflow_a,
        (incr_valid && value_temp > MaxValue) |-> (value_next == (value_temp - MaxValue - 1)))
    `BR_ASSERT_IMPL(
        maxvalue_plus_one_a,
        (!reinit && value == MaxValue && incr_valid && incr == 1'b1) |-> (value_next == 0))
  end

  // Increment corners
  `BR_ASSERT_IMPL(plus_zero_a, (!reinit && incr_valid && incr == '0) |-> (value_next == value))
  `BR_COVER_IMPL(increment_max_c, incr_valid && incr == MaxIncrement)
  `BR_COVER_IMPL(value_temp_oob_c, value_temp > MaxValue)

  // Reinit
  `BR_ASSERT_IMPL(reinit_no_incr_a, reinit && !incr_valid |=> value == $past(initial_value))
  `BR_COVER_IMPL(reinit_and_incr_c, reinit && incr_valid && incr > 0)

endmodule : br_counter_incr
