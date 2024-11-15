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
// This module prevents credit underflow by deasserting the decr_ready signal
// which insufficient credit is available.
//
// The user is responsible for ensuring the credit counter never overflows.
// This is checked by assertions.
//
// The actual data (flits) do not flow through this module.
//
// Resets to initial_value, which is a port rather than a parameter to accommodate
// designs where the initial value needs to be adjustable.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_counter #(
    // Maximum credit counter value (inclusive). Must be at least 1.
    parameter int MaxValue = 1,
    // Maximum increment/decrement amount (inclusive). Must be at least 1.
    parameter int MaxChange = 1,
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int ChangeWidth = $clog2(MaxChange + 1)
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

  // Ensure increments and decrements are in range
  `BR_ASSERT_INTG(incr_in_range_a, incr_valid |-> (incr <= MaxChange))
  `BR_ASSERT_INTG(decr_in_range_a, decr_valid |-> (decr <= MaxChange))

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

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  `BR_ASSERT_INTG(no_overflow_or_underflow_a, value_extended_next <= MaxValue)

  // Ensure the credit counter goes through the full range to help ensure
  // flow control corners are hit outside the module.
  `BR_COVER_INTG(value_reaches_zero_c, value == 0)
  `BR_COVER_INTG(value_reaches_max_c, value == MaxValue)

  // Ensure the initial value was within the valid range on the last cycle when exiting reset
  `BR_ASSERT_INTG(initial_value_in_range_a, $fell(rst) |-> $past(initial_value) <= MaxValue)

  // Withhold and available
  `BR_ASSERT_INTG(withhold_in_range_a, withhold <= MaxValue)
  `BR_COVER_INTG(withhold_c, withhold > 0)
  `BR_COVER_INTG(decr_gt_available_c, decr_valid && decr > available)

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

  `BR_REGIL(value, value_next, value_loaden, initial_value)

  // Withhold and available: don't use the decrement in the calculation of
  // available credits because that would cause a combinational loop
  assign available  = value_plus_incr > withhold ? value_plus_incr - withhold : '0;
  assign decr_ready = ValueWidth'(decr_internal) <= available;

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

  // Withhold and available
  `BR_COVER_IMPL(value_lt_available_c, value < available)
  `BR_COVER_IMPL(value_gt_available_c, value > available)
  `BR_COVER_IMPL(withhold_gt_value_c, withhold > value)

endmodule : br_credit_counter
