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
// It interfaces with a receiver using a ready/valid handshake for data transfer and a credit
// return mechanism for flow control.
//
// Push Interface:
//   - Accepts data to be sent (push_data) when push_valid is asserted.
//   - Indicates readiness to accept data via push_ready, which is high when there are available credits.
//
// Pop Interface:
//   - Credits are replenished when the receiver returns a credit (pop_credit asserted).
//   - pop_credit_stall is asserted during reset to prevent the receiver from returning credits prematurely.
//   - The receiver should not exit reset and assert pop_credit when pop_credit_stall is high, otherwise
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
//     and/or the pop-side interface (e.g., with br_delay_nr_valid) to help close timing.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_sender #(
    // Width of the datapath in bits. Must be at least 1.
    parameter int BitWidth = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least 1.
    parameter int MaxCredit = 1,
    localparam int CounterWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Reset value for the credit counter
    input logic [CounterWidth-1:0] initial_credit,

    // Ready/valid push interface.
    output logic push_ready,
    input logic push_valid,
    input logic [BitWidth-1:0] push_data,

    // Credit/valid pop interface.
    output logic pop_credit_stall,
    input logic pop_credit,
    output logic pop_valid,
    output logic [BitWidth-1:0] pop_data,
    output logic [CounterWidth-1:0] credit_count,
    output logic [CounterWidth-1:0] credit_count_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bitwidth_in_range_a, BitWidth >= 1)
  `BR_ASSERT_STATIC(max_credit_in_range_a, MaxCredit >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_credit_counter #(
      .MaxValue (MaxCredit),
      .MaxChange(1)
  ) br_credit_counter (
      .clk,
      .rst,
      .initial_value(initial_credit),
      .incr_valid(pop_credit),
      .incr(1'b1),
      .decr_valid(pop_valid),
      .decr(1'b1),
      .value(credit_count),
      .value_next(credit_count_next)
  );

  `BR_REGI(pop_credit_stall, 1'b0, 1'b1)
  assign push_ready = (credit_count > 0) || pop_credit;
  assign pop_valid  = push_ready && push_valid;
  assign pop_data   = push_data;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(pop_valid_a, pop_valid == (push_valid && push_ready))
  `BR_ASSERT_IMPL(pop_with_zero_credits_a,
                  credit_count == '0 && pop_valid |-> pop_credit && push_valid)
  `BR_ASSERT_IMPL(push_pop_unchanged_credit_count_a,
                  pop_valid && pop_credit |-> credit_count == credit_count_next)
  `BR_COVER_IMPL(pop_valid_and_pop_credit_c, pop_valid && pop_credit)

endmodule : br_credit_sender
