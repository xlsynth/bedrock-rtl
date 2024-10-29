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

module br_counter_decr #(
    parameter int MaxValue = 1,  // Must be at least 1. Inclusive. Also the initial value.
    parameter int MaxDecrement = 1,  // Must be at least 1 and at most MaxValue. Inclusive.
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int DecrementWidth = $clog2(MaxDecrement + 1)
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
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_decrement_gte_1_a, MaxDecrement >= 1)
  `BR_ASSERT_STATIC(max_decrement_lte_max_value_a, MaxDecrement <= MaxValue)

  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> decr <= MaxDecrement)
  `BR_ASSERT_INTG(initial_value_in_range_a, initial_value <= MaxValue)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int MaxValueP1 = MaxValue + 1;
  localparam bit IsMaxValueP1PowerOf2 = (MaxValueP1 & (MaxValueP1 - 1)) == 0;

  logic [ValueWidth-1:0] value_temp;

  assign value_temp = (reinit ? initial_value : value) - (decr_valid ? decr : '0);

  if (IsMaxValueP1PowerOf2) begin : gen_power_of_2
    // For MaxValueP1 being a power of 2, wrapping occurs naturally
    assign value_next = value_temp;

  end else begin : gen_non_power_of_2
    // For MaxValueP1 not being a power of 2, handle wrap-around explicitly
    localparam int Margin = ((2 ** ValueWidth) - 1) - MaxValue;
    logic [ValueWidth-1:0] value_temp_wrapped;
    assign value_temp_wrapped = value_temp - Margin;
    assign value_next = value_temp > MaxValue ? value_temp_wrapped : value_temp;

    // Case-specific implementation checks
    `BR_ASSERT_STATIC(margin_gte0_a, Margin > 0)
    `BR_ASSERT_IMPL(value_temp_wrapped_in_range_a, value_temp_wrapped <= MaxValue)
  end

  `BR_REGIL(value, value_next, decr_valid || reinit, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(value_in_range_a, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_a, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_a, ##1 value == $past(value_next))

  // Underflow corners
  `BR_ASSERT_IMPL(value_underflow_a,
                  decr_valid && value_temp > MaxValue |-> value_next == value_temp - MaxValue - 1)
  `BR_ASSERT_IMPL(zero_minus_one_a,
                  value == 0 && decr_valid && decr == 1'b1 |-> value_next == MaxValue)

  // Decrement corners
  `BR_ASSERT_IMPL(plus_zero_a, decr_valid && decr == '0 |-> value_next == value)
  `BR_COVER_IMPL(decrement_max_c, decr_valid && decr == MaxDecrement)
  `BR_COVER_IMPL(value_temp_oob_c, value_temp > MaxValue)

  // Reinit
  `BR_ASSERT_IMPL(reinit_no_decr_a, reinit && !decr_valid |=> value == $past(initial_value))
  `BR_COVER_IMPL(reinit_and_decr_c, reinit && decr_valid && decr > 0)

endmodule : br_counter_decr
