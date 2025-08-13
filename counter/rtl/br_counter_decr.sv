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

// Bedrock-RTL Decrementing Counter
//
// A simple counter that decrements by a potentially variable amount each cycle,
// where the maximum decrement is given by MaxDecrement (inclusive).
// Underflows (wraps around past 0) up to MaxValue (inclusive), even if MaxValue + 1
// isn't a power-of-2. In the common case where MaxValue + 1 is a power-of-2,
// the implementation is simplified.
//
// When there is a valid decrement and it underflows:
//   value_next = (value - decr) % (MaxValue + 1)
//
// The counter state is exposed in two ways.
// (1) value holds the current counter state. There is a latency of 1 cycle from
//     a valid decrement to the counter state being updated.
// (2) value_next is what value will be on the next cycle. It is conditioned on
//     decr_valid: if low, then value_next == value. This is useful for constructing
//     single-cycle chains of counters.
// value and value_next are always valid.
//
// The counter value resets to initial_value.
//
// The reinit port reinitializes the counter to initial_value.
// This does *nearly* the same thing as rst but is likely to be driven by completely different
// logic. Rather than having the user mix together an expression involving both rst and reinit,
// a separate port helps keep the user's reset code clean and correct. Also, unlike reset, the
// reinit can accommodate a decrement on the same cycle, i.e., the decrement
// applies to the initial value rather than the old value.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_counter_decr #(
    // Width of the MaxValue parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    // Must be at least 1.
    parameter int MaxValueWidth = 32,
    // Width of the MaxDecrement parameter.
    // You might need to override this if you need a counter that's larger than 32 bits.
    // Must be at least 1.
    parameter int MaxDecrementWidth = 32,
    // Must be at least 1. Inclusive. Also the initial value.
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    // Must be at least 1 and at most MaxValue. Inclusive.
    parameter logic [MaxDecrementWidth-1:0] MaxDecrement = 1,
    // If 1, then when reinit is asserted together with decr_valid,
    // the decrement is applied to the initial value rather than the current value, i.e.,
    // value_next == initial_value - applicable decr.
    // If 0, then when reinit is asserted together with decr_valid,
    // the decrement values are ignored, i.e., value_next == initial_value.
    parameter bit EnableReinitAndDecr = 1,
    // If 1, the counter value saturates at 0.
    // If 0, the counter value wraps around at 0.
    parameter bit EnableSaturate = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, cover the cases where reinit is asserted
    // If 0, assert that reinit is never asserted
    parameter bit EnableCoverReinit = 1,
    // If 1, then cover the cases where reinit is asserted together with incr_valid.
    // Otherwise, assert that reinit is never asserted together with incr_valid.
    parameter bit EnableCoverReinitAndDecr = EnableCoverReinit,
    // If 1, then cover the cases where reinit is asserted when incr_valid is 0.
    // If 0, assert that reinit always asserts along with incr_valid.
    parameter bit EnableCoverReinitNoDecr = EnableCoverReinit,
    // If 1, cover the case where decr_valid is 1 but decr is 0.
    // If 0, assert that decr is always non-zero when decr_valid is 1.
    parameter bit EnableCoverZeroDecrement = 1,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxDecrementP1Width = MaxDecrementWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int DecrementWidth = $clog2(MaxDecrementP1Width'(MaxDecrement) + 1)
) (
    // Posedge-triggered clock.
    input  logic                      clk,
    // Synchronous active-high reset.
    input  logic                      rst,
    input  logic                      reinit,
    input  logic [    ValueWidth-1:0] initial_value,
    input  logic                      decr_valid,
    input  logic [DecrementWidth-1:0] decr,
    output logic [    ValueWidth-1:0] value,
    output logic [    ValueWidth-1:0] value_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(max_value_width_gte_1_a, MaxValueWidth >= 1)
  `BR_ASSERT_STATIC(max_decrement_width_gte_1_a, MaxDecrementWidth >= 1)
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_decrement_gte_1_a, MaxDecrement >= 1)
  `BR_ASSERT_STATIC(max_decrement_lte_max_value_a, MaxDecrement <= MaxValue)

  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> decr <= MaxDecrement)
  `BR_ASSERT_INTG(initial_value_in_range_a, initial_value <= MaxValue)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_decr_valid_a, !decr_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam logic [MaxValueP1Width-1:0] MaxValueP1 = MaxValue + 1;
  localparam bit IsMaxValueP1PowerOf2 = (MaxValueP1 & (MaxValueP1 - 1)) == 0;

  logic [ValueWidth-1:0] value_temp;
  logic underflow;
  logic [ValueWidth-1:0] decr_ext;

  assign decr_ext = ValueWidth'(decr);

  if (EnableReinitAndDecr) begin : gen_reinit_and_decr
    logic [ValueWidth-1:0] base_value;
    assign base_value = reinit ? initial_value : value;
    assign value_temp = base_value - (decr_valid ? decr : '0);
    assign underflow  = decr_valid && (decr_ext > base_value);
  end else begin : gen_reinit_ignore_decr
    assign value_temp = reinit ? initial_value : (value - (decr_valid ? decr : '0));
    assign underflow  = !reinit && decr_valid && (decr_ext > value);
  end

  if (EnableSaturate) begin : gen_saturate
    assign value_next = underflow ? '0 : value_temp;

    // For MaxValueP1 being a power of 2, wrapping occurs naturally
  end else if (IsMaxValueP1PowerOf2) begin : gen_power_of_2_wrap
    assign value_next = value_temp;
    `BR_UNUSED(underflow)
  end else begin : gen_non_power_of_2_wrap
    // For MaxValueP1 not being a power of 2, handle wrap-around explicitly
    localparam logic [ValueWidth-1:0] Margin = ((2 ** ValueWidth) - 1) - MaxValue;
    logic [ValueWidth-1:0] value_temp_wrapped;
    assign value_temp_wrapped = value_temp - Margin;
    assign value_next = underflow ? value_temp_wrapped : value_temp;

    // Case-specific implementation checks
    `BR_ASSERT_STATIC(margin_gte0_a, Margin > 0)
    `BR_ASSERT_IMPL(value_temp_wrapped_in_range_on_underflow_a,
                    underflow |-> (value_temp_wrapped >= Margin))
  end

  `BR_REGLI(value, value_next, decr_valid || reinit, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(value_in_range_a, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_a, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_a, ##1 !$past(rst) |-> value == $past(value_next))

  // Underflow corners
  if (EnableSaturate) begin : gen_saturate_impl_checks
    `BR_ASSERT_IMPL(value_saturate_a,
                    (decr_valid && decr > value && !reinit) |-> (value_next == '0))
  end else begin : gen_overflow_impl_checks
    if (!IsMaxValueP1PowerOf2) begin : gen_value_underflow_assert
`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
      logic [ValueWidth-1:0] value_temp_adjusted;

      // If there is an underflow, we can treat value_temp as a negative number.
      // By adding MaxValue + 1 to it, we should get to the correct wrap-around value.
      assign value_temp_adjusted = value_temp + ValueWidth'(MaxValue + 1);
`endif
`endif
      `BR_ASSERT_IMPL(value_underflow_a,
                      (decr_valid && value_temp > MaxValue) |-> (value_next == value_temp_adjusted))
    end
    `BR_ASSERT_IMPL(
        zero_minus_one_a,
        (!reinit && value == 0 && decr_valid && decr == 1'b1) |-> (value_next == MaxValue))
  end

  // Decrement corners
  if (EnableCoverZeroDecrement) begin : gen_cover_zero_decrement
    `BR_ASSERT_IMPL(plus_zero_a, (!reinit && decr_valid && decr == '0) |-> (value_next == value))
  end else begin : gen_assert_no_zero_decrement
    `BR_ASSERT_IMPL(no_plus_zero_a, decr_valid |-> decr > '0)
  end
  `BR_COVER_IMPL(decrement_max_c, decr_valid && decr == MaxDecrement)
  if (!IsMaxValueP1PowerOf2) begin : gen_value_temp_oob_cover
    `BR_COVER_IMPL(value_temp_oob_c, value_temp > MaxValue)
  end

  // Reinit
  if (EnableCoverReinit) begin : gen_cover_reinit
    if (EnableCoverReinitNoDecr) begin : gen_cover_reinit_no_decr
      `BR_ASSERT_IMPL(reinit_no_decr_a, reinit && !decr_valid |=> value == $past(initial_value))
    end else begin : gen_assert_no_reinit_without_decr
      `BR_ASSERT_IMPL(no_reinit_without_decr_a, reinit |-> decr_valid)
    end
    if (EnableCoverReinitAndDecr) begin : gen_cover_reinit_and_decr
      `BR_COVER_IMPL(reinit_and_decr_c, reinit && decr_valid && decr > 0)
    end else begin : gen_assert_no_reinit_and_decr
      `BR_ASSERT_IMPL(no_reinit_and_decr_a, reinit |-> !decr_valid)
    end
  end else begin : gen_assert_no_reinit
    `BR_ASSERT_IMPL(no_reinit_a, !reinit)
  end

endmodule : br_counter_decr
