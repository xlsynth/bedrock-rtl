// Copyright 2024 The Bedrock-RTL Authors
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
    parameter int MaxValue = 1,  // Must be at least 1. Inclusive.
    parameter int MaxChange = 1,  // Must be at least 1 and at most MaxValue. Inclusive.
    // If 1, allow the counter value to wrap around 0/MaxValue, adding additional correction
    // logic to do so if MaxValue is not 1 less than a power of two.
    // If 0, don't allow wrapping and omit overflow/underflow correction logic.
    // Assert there is no overflow/underflow.
    parameter bit EnableWrap = 1,
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int ChangeWidth = $clog2(MaxChange + 1)
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
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_increment_gte_1_a, MaxChange >= 1)
  `BR_ASSERT_STATIC(max_increment_lte_max_value_a, MaxChange <= MaxValue)

  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> incr <= MaxChange)
  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> decr <= MaxChange)
  `BR_ASSERT_INTG(initial_value_in_range_a, initial_value <= MaxValue)

  // Assertion-only helper logic for overflow/underflow detection
`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  localparam int ExtWidth = $clog2(MaxValue + ChangeWidth + 1);
  logic [ExtWidth-1:0] value_extended;
  logic [ExtWidth-1:0] value_extended_next;

  // ri lint_check_waive IFDEF_CODE
  assign value_extended = ExtWidth'(value);
  // ri lint_check_waive IFDEF_CODE
  assign value_extended_next =
      // ri lint_check_waive ARITH_ARGS
      value_extended + (incr_valid ? incr : '0) - (decr_valid ? decr : '0);

  if (EnableWrap) begin : gen_wrap_cover
    `BR_COVER_INTG(overflow_or_underflow_c, value_extended_next > MaxValue)
  end else begin : gen_no_wrap_assert
    `BR_ASSERT_INTG(no_overflow_or_underflow_a, value_extended_next <= MaxValue)
  end
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int MaxValueP1 = MaxValue + 1;
  localparam bit IsMaxValueP1PowerOf2 = (MaxValueP1 & (MaxValueP1 - 1)) == 0;
  localparam int TempWidth = $clog2(MaxValue + MaxChange + 1);

  logic                   value_loaden;
  logic [  TempWidth-1:0] value_temp_incr;
  // The MSB might not be used
  // ri lint_check_waive INEFFECTIVE_NET
  logic [  TempWidth-1:0] value_temp;
  logic [ ValueWidth-1:0] base_value;
  logic [ChangeWidth-1:0] incr_qual;
  logic [ChangeWidth-1:0] decr_qual;

  assign base_value = reinit ? initial_value : value;
  assign incr_qual = incr_valid ? incr : '0;
  assign decr_qual = decr_valid ? decr : '0;
  assign value_temp_incr = base_value + incr_qual;
  assign value_temp = value_temp_incr - TempWidth'(decr_qual);
  assign value_loaden = reinit || incr_valid || decr_valid;

  // For MaxValueP1 being a power of 2, wrapping occurs naturally
  if (IsMaxValueP1PowerOf2 || !EnableWrap) begin : gen_no_wrap
    assign value_next = value_temp[ValueWidth-1:0];

    if (TempWidth > ValueWidth) begin : gen_unused
      `BR_UNUSED_NAMED(value_temp_msbs, value_temp[TempWidth-1:ValueWidth])
    end
    // For MaxValueP1 not being a power of 2, handle wrap-around explicitly
  end else begin : gen_wrap
    // The MSB will not be used
    // ri lint_check_waive INEFFECTIVE_NET
    logic [TempWidth-1:0] value_temp_wrapped;
    logic                 is_net_decr;
    logic                 will_wrap;
    logic                 will_underflow;
    logic                 will_overflow;

    assign is_net_decr = decr_qual > incr_qual;
    assign will_wrap = value_temp > MaxValue;
    assign will_underflow = will_wrap && is_net_decr;
    assign will_overflow = will_wrap && !is_net_decr;

    assign value_temp_wrapped =
        will_underflow ? (value_temp + MaxValueP1) :
        will_overflow  ? (value_temp - MaxValueP1) :
                         value_temp;
    // If TempWidth == ValueWidth, the bit select covers the full range
    // ri lint_check_waive FULL_RANGE
    assign value_next = value_temp_wrapped[ValueWidth-1:0];

    if (TempWidth > ValueWidth) begin : gen_unused
      `BR_UNUSED_NAMED(value_temp_wrapped_msbs, value_temp_wrapped[TempWidth-1:ValueWidth])
    end
  end

  `BR_REGIL(value, value_next, value_loaden, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(value_in_range_a, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_a, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_a, ##1 value == $past(value_next))

  // Change corners
  `BR_COVER_IMPL(increment_max_c, incr_valid && incr == MaxChange)
  `BR_COVER_IMPL(increment_min_c, incr_valid && incr == '0)
  `BR_COVER_IMPL(decrement_max_c, decr_valid && decr == MaxChange)
  `BR_COVER_IMPL(decrement_min_c, decr_valid && decr == '0)
  `BR_COVER_IMPL(increment_and_decrement_c, incr_valid && incr > '0 && decr_valid && decr > '0)

  // Reinit
  `BR_COVER_IMPL(reinit_and_change_c, reinit && (incr_valid || decr_valid))

endmodule : br_counter
