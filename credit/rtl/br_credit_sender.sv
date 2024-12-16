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

// Bedrock-RTL Credit Sender
//
// Manages the sender side of a credit-based flow control mechanism.
// Converts from ready/valid on the push interface to credit/valid on the pop interface.
//
// Push Interface:
//   - Accepts data to be sent (push_data) when push_valid is asserted.
//   - Indicates readiness to accept data via push_ready, which is high when there are available credits.
//
// Pop Interface:
//   - Credits are replenished when the receiver returns a credit (pop_credit asserted).
//   - pop_reset_active_fwd is asserted during reset to prevent the receiver from returning credits prematurely
//     and to indicate that the receiver's credit count should be reset.
//   - pop_reset_active_rev is asserted by the receiver to indicate that the receiver is in reset
//     the sender will reset its credit count to the initial value and block sending any data until
//     the pop_reset_active_rev is deasserted.
//   - The receiver should not exit reset and assert pop_credit when pop_reset_active_fwd is high, otherwise
//     credits will be lost.
//   - Forwards data to the receiver via pop_data and asserts pop_valid when both push_valid and push_ready
//     are high.
//
// Credit Tracking (credit_count):
//   - Uses an internal credit counter to track the number of available credits.
//   - Initializes to initial_credit, allowing for adjustable initial credit values.
//
// Flow Control Mechanism:
//   - Decrements the credit count when a flit (data packet) is sent (pop_valid asserted).
//   - Increments the credit count when a credit is received from the receiver (pop_credit asserted).
//   - Data is only sent when there are available credits or a credit is being replenished the
//     same cycle.
//
// Latency:
//   - There are no registers on the datapath between the push and pop interfaces.
//   - There is a cut-through latency of 0 cycles from push to pop.
//   - There is a backpressure latency of 0 cycles from pop to push.
//   - Credits can be spent the same cycle that they are replenished.
//   - Users will likely want to register the push-side interface (e.g., with br_flow_reg_*)
//     and/or the pop-side interface (e.g., with br_delay_valid) to help close timing.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_sender #(
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least 1.
    parameter int MaxCredit = 1,
    // If 1, add retiming to pop_valid and pop_data
    parameter bit RegisterPopOutputs = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int CounterWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Ready/valid push interface.
    output logic push_ready,
    input logic push_valid,
    input logic [Width-1:0] push_data,

    // Credit/valid pop interface.
    output logic pop_reset_active_fwd,
    input logic pop_reset_active_rev,
    input logic pop_credit,
    output logic pop_valid,
    output logic [Width-1:0] pop_data,

    // Reset value for the credit counter
    input  logic [CounterWidth-1:0] credit_initial,
    // Dynamically withhold credits from circulation
    input  logic [CounterWidth-1:0] credit_withhold,
    // Credit counter state before increment/decrement/withhold.
    output logic [CounterWidth-1:0] credit_count,
    // Dynamic amount of available credit.
    output logic [CounterWidth-1:0] credit_available
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_in_range_a, Width >= 1)
  `BR_ASSERT_STATIC(max_credit_in_range_a, MaxCredit >= 1)

  br_flow_checks_valid_data #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability)
  ) br_flow_checks_valid_data (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_credit_counter #(
      .MaxValue (MaxCredit),
      .MaxChange(1)
  ) br_credit_counter (
      .clk,
      .rst,
      .incr_valid(pop_credit),
      .incr(1'b1),
      .decr_ready(push_ready),
      .decr_valid(push_valid),
      .decr(1'b1),
      .reinit(pop_reset_active_rev),
      .initial_value(credit_initial),
      .withhold(credit_withhold),
      .value(credit_count),
      .available(credit_available)
  );

  `BR_REGI(pop_reset_active_fwd, 1'b0, 1'b1)

  logic internal_pop_valid;
  assign internal_pop_valid = push_ready && push_valid;

  if (RegisterPopOutputs) begin : gen_reg_pop
    `BR_REG(pop_valid, internal_pop_valid)
    `BR_REGL(pop_data, push_data, internal_pop_valid)
  end else begin : gen_passthru_pop
    assign pop_valid = internal_pop_valid;
    assign pop_data  = push_data;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(pop_follows_push_a,
                  (push_valid && push_ready) |-> ##(RegisterPopOutputs) pop_valid)
  `BR_ASSERT_IMPL(pop_with_zero_credits_a,
                  credit_count == '0 && internal_pop_valid |-> pop_credit && push_valid)
  `BR_ASSERT_IMPL(push_pop_unchanged_credit_count_a,
                  internal_pop_valid && pop_credit |=> credit_count == $past(credit_count))
  `BR_ASSERT_IMPL(withhold_and_spend_a,
                  credit_count == credit_withhold && internal_pop_valid |-> pop_credit)
  `BR_COVER_IMPL(pop_valid_and_pop_credit_c, pop_valid && pop_credit)

  // Rely on submodule implementation checks

endmodule : br_credit_sender
