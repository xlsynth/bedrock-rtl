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
// The value resets to MaxValue.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_counter_decr #(
    parameter int MaxValue = 1,  // Must be at least 1. Inclusive. Also the initial value.
    parameter int MaxDecrement = 1,  // Must be at least 1. Inclusive.
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int DecrementWidth = $clog2(MaxDecrement + 1)
) (
    input  logic                      clk,
    input  logic                      rst,
    input  logic                      decr_valid,
    input  logic [DecrementWidth-1:0] decr,
    output logic [    ValueWidth-1:0] value,
    output logic [    ValueWidth-1:0] value_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(MaxValue_gte_1_A, MaxValue >= 1)
  `BR_ASSERT_STATIC(MaxDecrement_gte_1_A, MaxDecrement >= 1)

  `BR_ASSERT_INTG(decr_in_range_A, decr_valid |-> decr <= MaxDecrement)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int MaxValuePlusOne = MaxValue + 1;
  localparam bit IsMaxValuePlusOnePowerOf2 = (MaxValuePlusOne & (MaxValuePlusOne - 1)) == 0;

  logic [ValueWidth-1:0] value_next_internal;
  logic [ValueWidth-1:0] value_temp;

  assign value_temp = value - decr;

  if (IsMaxValuePlusOnePowerOf2) begin : gen_power_of_2
    // For MaxValuePlusOne being a power of 2, wrapping occurs naturally
    assign value_next_internal = decr_valid ? value_temp : value;

  end else begin : gen_non_power_of_2
    // For MaxValuePlusOne not being a power of 2, handle wrap-around explicitly
    localparam int Margin = 2 ** ValueWidth - 1 - MaxValue;
    logic [ValueWidth-1:0] value_temp_wrapped;
    assign value_temp_wrapped  = value_temp - Margin;
    assign value_next_internal = value_temp >= MaxValue ? value_temp_wrapped : value_temp;

    // Case-specific implementation checks
    `BR_ASSERT_STATIC(Margin_gte0_A, Margin > 0)
    `BR_ASSERT_IMPL(value_temp_wrapped_in_range_A, value_temp_wrapped <= MaxValue)
  end

  // If the user leaves the value_next port unused, then the synthesis tool
  // should be able to automatically simplify the following ternary expression
  // to just value_next_internal, because the load-enable on the register is
  // conditioned on the same decr_valid.
  assign value_next = decr_valid ? value_next_internal : value;
  `BR_REGIL(value, value_next, decr_valid, MaxValue)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(reset_to_MaxValue_A, $fell(rst) |-> value == MaxValue)
  `BR_ASSERT_IMPL(value_in_range_A, value <= MaxValue)
  `BR_ASSERT_IMPL(value_next_in_range_A, value_next <= MaxValue)
  `BR_ASSERT_IMPL(value_next_propagates_A, ##1 value == $past(value_next))
  `BR_ASSERT_IMPL(value_wrap_A,
                  decr_valid && value_temp > MaxValue |-> value_next == value_temp - MaxValue - 1)
  `BR_ASSERT_IMPL(maxvalue_plus_one_A,
                  value == MaxValue && decr_valid && decr == 1'b1 |-> value_next == 0)
  `BR_ASSERT_IMPL(plus_zero_A, decr_valid && decr == '0 |-> value_next == value)
  `BR_COVER_IMPL(decrement_max_C, decr_valid && decr == MaxDecrement)
  `BR_COVER_IMPL(value_temp_oob_C, value_temp > MaxValue)

endmodule : br_counter_decr
