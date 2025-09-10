// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL VC-based Credit Sender
//
// This module implements a credit sender for a single physical channel
// that is shared by multiple virtual channels, with each VC having its
// own dedicated credit return.
//
// It takes N ready/valid interfaces, one for each of VC, and presents
// the VCs that have credit available for arbitration by an external arbiter.
// The winning VC will have its data sent on the shared physical channel
// and its credit count will be decremented.

`include "br_asserts_internal.svh"

module br_credit_sender_vc #(
    // Number of virtual channels sharing this credit sender.
    // Must be at least 2.
    parameter int NumVcs = 2,
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored per VC (inclusive).
    // Must be at least 1.
    parameter int MaxCredit = 1,
    // Maximum number of credits that can be returned in a single cycle.
    // Must be at least 1 but at most MaxCredit.
    parameter int PopCreditMaxChange = 1,
    // If 1, add 1 cycle of retiming to pop outputs.
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
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, then at the end of simulation, assert that the credit counter value equals
    // the maximum number of credits that it stored at any point during the test.
    parameter bit EnableAssertFinalMaxValue = 1,

    localparam int VcWidth = $clog2(NumVcs),
    localparam int CounterWidth = $clog2(MaxCredit + 1),
    localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Interface to external arbiter
    output logic [NumVcs-1:0] request,
    // The can_grant signal indicates for each VC that there are no
    // higher priority VCs active, so that VC will win arbitration if
    // it is requesting. The invariant `(request & can_grant) == grant`
    // must always be satisfied.
    input  logic [NumVcs-1:0] can_grant,
    input  logic [NumVcs-1:0] grant,
    output logic              enable_priority_update,

    // Ready/valid push interface per VC.
    output logic [NumVcs-1:0]            push_ready,
    input  logic [NumVcs-1:0]            push_valid,
    input  logic [NumVcs-1:0][Width-1:0] push_data,

    // Credit/valid pop interface.
    // Indicates that this module is in reset.
    // Synchronous active-high.
    output logic                                   pop_sender_in_reset,
    // Indicates that the receiver is in reset.
    // Synchronous active-high.
    input  logic                                   pop_receiver_in_reset,
    input  logic [ NumVcs-1:0][PopCreditWidth-1:0] pop_credit,
    output logic                                   pop_valid,
    output logic [  Width-1:0]                     pop_data,
    output logic [VcWidth-1:0]                     pop_vc,

    // Reset value for the credit counter
    input  logic [NumVcs-1:0][CounterWidth-1:0] credit_initial,
    // Dynamically withhold credits from circulation
    input  logic [NumVcs-1:0][CounterWidth-1:0] credit_withhold,
    // Credit counter state before increment/decrement/withhold.
    output logic [NumVcs-1:0][CounterWidth-1:0] credit_count,
    // Dynamic amount of available credit.
    output logic [NumVcs-1:0][CounterWidth-1:0] credit_available
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_vcs_in_range_a, (NumVcs >= 2))
  `BR_ASSERT_STATIC(pop_credit_max_change_in_range_a, (PopCreditMaxChange <= MaxCredit))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int ChangeWidth = $clog2(PopCreditMaxChange + 1);

  logic either_rst;
  assign either_rst = rst || pop_receiver_in_reset;

  logic [NumVcs-1:0] mux_push_valid;
  logic [NumVcs-1:0] mux_push_ready;

  logic [NumVcs-1:0] credit_decr_ready;
  logic [NumVcs-1:0] credit_decr_valid;
  logic [NumVcs-1:0][ChangeWidth-1:0] credit_decr;

  logic [NumVcs-1:0] credit_incr_valid;
  logic [NumVcs-1:0][ChangeWidth-1:0] credit_incr;

  for (genvar i = 0; i < NumVcs; i++) begin : gen_credit_counters
    assign credit_incr_valid[i] = |pop_credit[i];
    assign credit_incr[i] = pop_credit[i];
    assign credit_decr[i] = ChangeWidth'(1'b1);
    assign credit_decr_ready[i] = credit_available[i] > '0;

    br_credit_counter #(
        .MaxValue(MaxCredit),
        .MaxChange(PopCreditMaxChange),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableAssertFinalMaxValue(EnableAssertFinalMaxValue),
        .EnableAssertFinalMinValue(EnableAssertFinalMinValue)
    ) br_credit_counter (
        .clk,
        .rst(either_rst),
        .incr_valid(credit_incr_valid[i]),
        .incr(credit_incr[i]),
        .decr_ready(),  // Can't use this because of possible combinational loop
        .decr_valid(credit_decr_valid[i]),
        .decr(credit_decr[i]),
        .initial_value(credit_initial[i]),
        .withhold(credit_withhold[i]),
        .value(credit_count[i]),
        .available(credit_available[i])
    );

    br_flow_fork #(
        .NumFlows(2),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_fork_push (
        .clk,
        .rst,
        .push_valid(push_valid[i]),
        .push_ready(push_ready[i]),
        .pop_valid_unstable({credit_decr_valid[i], mux_push_valid[i]}),
        .pop_ready({credit_decr_ready[i], mux_push_ready[i]})
    );
  end

  logic internal_pop_valid;
  logic [Width-1:0] internal_pop_data;
  logic [VcWidth-1:0] internal_pop_vc;

  br_flow_mux_core #(
      .NumFlows(NumVcs),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core_push (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready(mux_push_ready),
      .push_valid(mux_push_valid),
      .push_data,
      .pop_ready(1'b1),
      .pop_valid_unstable(internal_pop_valid),
      .pop_data_unstable(internal_pop_data)
  );

  br_enc_onehot2bin #(
      .NumValues(NumVcs),
      .BinWidth (VcWidth)
  ) br_enc_onehot2bin_pop_vc (
      .clk,
      .rst,
      .in(grant),
      .out_valid(),
      .out(internal_pop_vc)
  );

  br_delay_valid #(
      .Width(Width + VcWidth),
      .NumStages(RegisterPopOutputs)
  ) br_delay_valid_pop (
      .clk,
      .rst,
      .in_valid(internal_pop_valid),
      .in({internal_pop_data, internal_pop_vc}),
      .out_valid(pop_valid),
      .out({pop_data, pop_vc}),
      .out_valid_stages(),
      .out_stages()
  );

  br_delay_nr #(
      .Width(1),
      .NumStages(RegisterPopOutputs)
  ) br_delay_nr_pop_sender_in_reset (
      .clk,
      .in(rst),
      .out(pop_sender_in_reset),
      .out_stages()
  );

endmodule
