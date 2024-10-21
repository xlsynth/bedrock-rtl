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

// Bedrock-RTL Credit Counter
//
// Tracks a pool of credits used for long-distance flow control.
// It can be instantiated on either the sender or receiver side.
// For example, the sender side behavior is to increment when a
// a credit is replenished from the receiver, and decrement when
// a flit it sent; the receiver side behavior is to increment
// when a flit is received and decrement when returning a credit to
// the sender.
//
// The counter supports parameterized increments and decrements, with
// MaxChange defining the maximum inclusive change amount (default is 1).
// The maximum inclusive credit counter value is defined by MaxValue (default
// is 1). The counter can increment and decrement on the same cycle, potentially
// by different amounts.
//
// The user is responsible for ensuring the credit counter never overflows or
// underflows. This is checked by assertions.
//
// The actual data (flits) do not flow through this module.
//
// Resets to initial_value, which is a port rather than a parameter to accommodate
// designs where the initial value needs to be adjustable.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_counter #(
    parameter int MaxValue = 1,  // Maximum credit counter value (inclusive). Default is 1.
    parameter int MaxChange = 1,  // Maximum increment/decrement amount (inclusive). Default is 1.
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int ChangeWidth = $clog2(MaxChange + 1)
) (
    // Posedge-triggered clock.
    input  logic                   clk,
    // Synchronous active-high reset.
    input  logic                   rst,
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

  // Parameter checks
  `BR_ASSERT_STATIC(max_value_gte_1_a, MaxValue >= 1)
  `BR_ASSERT_STATIC(max_change_gte_1_a, MaxChange >= 1)
  `BR_ASSERT_STATIC(max_change_lte_max_value_a, MaxChange <= MaxValue)

  // Ensure the initial value was within the valid range on the last cycle when exiting reset
  `BR_ASSERT_COMB_INTG(initial_value_in_range_a, $fell(rst) |-> $past(initial_value) <= MaxValue)

  // Ensure increments and decrements are in range
  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> (incr <= MaxChange))
  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> (decr <= MaxChange))

  // Assertion-only helper logic for overflow/underflow detection
`ifdef SV_ASSSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  localparam int CalcWidth = ValueWidth + 1;
  logic [CalcWidth-1:0] value_extended_next;

  // Compute the next value with extended width
  always_comb begin
    value_extended_next = {1'b0, value};
    if (incr_valid) value_extended_next = value_extended_next + incr;
    if (decr_valid) value_extended_next = value_extended_next - decr;
  end
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // SV_ASSERT_ON

  `BR_ASSERT_INTG(no_overflow_or_underflow_a, value_extended_next <= MaxValue)

  // Ensure the credit counter goes through the full range to help ensure
  // flow control corners are hit outside the module.
  `BR_COVER_INTG(value_reaches_zero_c, value == 0)
  `BR_COVER_INTG(value_reaches_max_c, value == MaxValue)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [ValueWidth-1:0] incr_internal;
  logic [ValueWidth-1:0] decr_internal;

  assign incr_internal = incr_valid ? incr : '0;
  assign decr_internal = decr_valid ? decr : '0;
  assign value_next = value + incr_value - decr_value;

  // Register the value with synchronous reset to initial_value
  `BR_REGI(value, value_next, initial_value)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Reset
  `BR_ASSERT_IMPL(reset_behavior_a, $fell(rst) |-> value == $past(initial_value))

  // Value basics
  `BR_ASSERT_IMPL(value_next_a, value_next == value_extended_next[ValueWidth-1:0])
  `BR_ASSERT_IMPL(value_updates_a, ##1 value == $past(value_next))

  // Increment corners
  `BR_COVER_IMPL(max_incr_c, incr_valid && incr == MaxChange)
  `BR_COVER_IMPL(min_incr_c, incr_valid && incr == 0)

  // Decrement corners
  `BR_COVER_IMPL(max_decr_c, decr_valid && decr == MaxChange)
  `BR_COVER_IMPL(min_decr_c, decr_valid && decr == 0)

  // Increment/decrement combination corner cases
  `BR_COVER_IMPL(incr_and_decr_c, incr_valid && decr_valid)
  `BR_ASSERT_IMPL(incr_and_no_decr_c, incr_valid && !decr_valid |-> value_next >= value)
  `BR_ASSERT_IMPL(no_incr_and_decr_c, !incr_valid && decr_valid |-> value_next <= value)

  // No-op corners
  `BR_ASSERT_IMPL(idle_noop_a, !incr_valid && !decr_valid |-> value == value_next)
  `BR_ASSERT_IMPL(active_noop_a, incr_valid && decr_valid && incr == decr |-> value == value_next)

endmodule : br_credit_counter
