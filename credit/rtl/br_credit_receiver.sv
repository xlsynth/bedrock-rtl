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
//
// Reset:
//   - If either this sender or the receiver resets, then the other side must also reset
//     to ensure they collectively have a coherent view of the total credits and an empty receiver
//     buffer.
//     - If there is no reset skew between sender and receiver, the push_sender_in_reset and
//       push_receiver_in_reset ports can be tied off to 0/left unused.
//     - If there is reset skew between sender and receiver, or if they are in different reset domains,
//       then the push_sender_in_reset and push_receiver_in_reset signals should be connected accordingly
//       between sender and receiver.
//     - Note that this is *NOT* a general-purpose substitute for a higher-level reset protocol and
//       architectural reset domain crossing (RDC). All it does is make sure the sender and receiver
//       can be reset with skew or completely independently without causing a permanent loss of credits and
//       broken flow control.
//   - When in reset (the rst port and/or the push_receiver_in_reset port is high), this module:
//     - Ignores (drops) any incoming push valids.
//     - Does not send output credits on the push interface.
//     - Ignores (drops) any incoming pop credits.
//     - Does not send output valids on the pop interface.
//     - Loads the initial value for the credit counter from the credit_initial port.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_receiver #(
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least 1.
    parameter int MaxCredit = 1,
    // If 1, add 1 cycle of retiming to push outputs.
    parameter bit RegisterPushOutputs = 0,
    // Maximum pop credits that can be returned in a single cycle.
    // Must be at least 1 but cannot be greater than MaxCredit.
    parameter int PopCreditMaxChange = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int CounterWidth = $clog2(MaxCredit + 1),
    localparam int PopCreditChangeWidth = $clog2(PopCreditMaxChange + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Credit/valid push interface.
    // Indicates that the sender is in reset.
    // Synchronous active-high.
    input logic push_sender_in_reset,
    // Indicates that this module is in reset.
    // Synchronous active-high.
    output logic push_receiver_in_reset,
    input logic push_credit_stall,
    output logic push_credit,
    input logic push_valid,
    input logic [Width-1:0] push_data,

    // Credit/valid pop interface.
    // Unlike the push interface it has no credit stall mechanism.
    // Intended to be connected directly to a receiver buffer with
    // no reset skew.
    input  logic [PopCreditChangeWidth-1:0] pop_credit,
    output logic                            pop_valid,
    output logic [               Width-1:0] pop_data,

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
  `BR_ASSERT_STATIC(pop_credit_change_in_range_a,
                    (PopCreditMaxChange >= 1) && (PopCreditMaxChange <= MaxCredit))

  `BR_ASSERT_INTG(no_push_valid_if_no_credit_released_a, credit_count == MaxCredit |-> !push_valid)
  `BR_ASSERT_INTG(pop_credit_in_range_a, pop_credit <= PopCreditMaxChange)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_push_valid_a, !push_valid)
    `BR_ASSERT_FINAL(final_not_pop_valid_a, !pop_valid)
  end

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic either_rst;
  assign either_rst = rst || push_sender_in_reset;

  logic credit_decr_valid;
  logic credit_decr_ready;
  logic push_credit_internal;
  logic credit_incr_valid;

  br_credit_counter #(
      .MaxValue(MaxCredit),
      .MaxChange(PopCreditMaxChange),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_credit_counter (
      .clk,
      .rst(either_rst),
      .incr_valid(credit_incr_valid),
      .incr(pop_credit),
      .decr_ready(credit_decr_ready),
      .decr_valid(credit_decr_valid),
      .decr(PopCreditChangeWidth'(1'b1)),
      .initial_value(credit_initial),
      .withhold(credit_withhold),
      .value(credit_count),
      .available(credit_available)
  );

  assign credit_incr_valid = |pop_credit;

  assign credit_decr_valid = !push_credit_stall;
  assign push_credit_internal = credit_decr_valid && credit_decr_ready && !either_rst;

  assign pop_valid = push_valid && !either_rst;
  assign pop_data = push_data;

  if (RegisterPushOutputs) begin : gen_reg_push
    `BR_REGI(push_receiver_in_reset, 1'b0, 1'b1)
    `BR_REG(push_credit, push_credit_internal)
  end else begin : gen_passthru_push
    assign push_receiver_in_reset = rst;
    assign push_credit = push_credit_internal;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(push_credit_stall_a, push_credit_stall |-> !push_credit_internal)
  `BR_COVER_IMPL(passthru_credit_c, pop_credit && push_credit_internal && credit_count == '0)
  `BR_COVER_IMPL(passthru_credit_nonzero_count_c,
                 pop_credit && push_credit_internal && credit_count > '0)
  `BR_ASSERT_IMPL(over_withhold_a, credit_withhold > credit_count |-> !push_credit_internal)
  `BR_ASSERT_IMPL(withhold_and_release_a,
                  credit_count == credit_withhold && push_credit_internal |-> pop_credit)

  // Reset
  `BR_ASSERT_IN_RST_IMPL(push_receiver_in_reset_a, push_receiver_in_reset)
  `BR_ASSERT_IN_RST_IMPL(push_credit_0_in_reset_a, !push_credit)
  `BR_ASSERT_IN_RST_IMPL(pop_valid_0_in_reset_a, !pop_valid)

  // Reset handshake
  `BR_ASSERT_IMPL(push_sender_in_reset_no_pop_valid_a, push_sender_in_reset |-> !pop_valid)
  if (RegisterPushOutputs) begin : gen_assert_push_reg
    `BR_ASSERT_IMPL(push_sender_in_reset_no_push_credit_a, push_sender_in_reset |=> !push_credit)
  end else begin : gen_assert_push_no_reg
    `BR_ASSERT_IMPL(push_sender_in_reset_no_push_credit_a, push_sender_in_reset |-> !push_credit)
  end

  // Rely on submodule implementation checks

endmodule : br_credit_receiver
