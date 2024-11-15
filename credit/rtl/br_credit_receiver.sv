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

// Bedrock-RTL Credit Receiver
//
// Manages the receiver side of a credit-based flow control mechanism.
// Both the push and pop interfaces use credit/valid flow control.
//
// The push side is intended for delayed communication with a
// sender over multiple cycles where there may be reset skew between
// sender and receiver.
//
// The pop side must directly connect to a dedicated buffer (managed with
// the credits). There must be no reset skew between this module and
// the receiver buffer attached to the pop interface.
//
// This module does not include any buffering on the datapath.
//
// In most cases, you will want to use br_fifo_*_push_credit instead,
// since it bundles this module with the receiver buffer logic.
//
// Latency:
//   - There are no registers on the datapath between the push and pop interfaces.
//   - There is a cut-through latency of 0 cycles from push to pop.
//   - There is a backpressure latency of 0 cycles from pop to push.
//   - Credits can be released the same cycle that they are acquired from the receiver buffer.
//   - Users will likely want to register the push-side interface (e.g., with br_delay_valid).

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_receiver #(
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least 1.
    parameter int MaxCredit = 1,
    // If 1, add retiming to push_credit
    parameter bit RegisterPushCredit = 0,
    localparam int CounterWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Credit/valid push interface.
    input logic push_credit_stall,
    output logic push_credit,
    input logic push_valid,
    input logic [Width-1:0] push_data,

    // Credit/valid pop interface.
    // Unlike the push interface it has no credit stall mechanism.
    // Intended to be connected directly to a receiver buffer with
    // no reset skew.
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

  `BR_ASSERT_INTG(no_push_valid_if_no_credit_released_a, credit_count == MaxCredit |-> !push_valid)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic credit_decr_valid;
  logic credit_decr_ready;
  logic push_credit_internal;

  br_credit_counter #(
      .MaxValue (MaxCredit),
      .MaxChange(1)
  ) br_credit_counter (
      .clk,
      .rst,
      .incr_valid(pop_credit),
      .incr(1'b1),
      .decr_ready(credit_decr_ready),
      .decr_valid(credit_decr_valid),
      .decr(1'b1),
      .initial_value(credit_initial),
      .withhold(credit_withhold),
      .value(credit_count),
      .available(credit_available)
  );

  assign credit_decr_valid = !push_credit_stall;
  assign push_credit_internal = credit_decr_valid && credit_decr_ready;
  assign pop_valid = push_valid;
  assign pop_data = push_data;

  if (RegisterPushCredit) begin : gen_reg_push
    `BR_REG(push_credit, push_credit_internal)
  end else begin : gen_passthru_push
    assign push_credit = push_credit_internal;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(push_credit_stall_a, push_credit_stall |-> !push_credit)
  `BR_COVER_IMPL(passthru_credit_c, pop_credit && push_credit && credit_count == '0)
  `BR_COVER_IMPL(passthru_credit_nonzero_count_c, pop_credit && push_credit && credit_count > '0)
  `BR_ASSERT_IMPL(over_withhold_a, credit_withhold > credit_count |-> !push_credit)
  `BR_ASSERT_IMPL(withhold_and_release_a,
                  credit_count == credit_withhold && push_credit |-> pop_credit)

  // Rely on submodule implementation checks

endmodule : br_credit_receiver
