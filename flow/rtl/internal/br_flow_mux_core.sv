// Copyright 2024-2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Flow-Controlled Multiplexer Core
//
// Combines core-priority arbitration with data path multiplexing.
// Grants a single request at a time with core priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// Stateful arbiter, but 0 latency from push to pop.
// The pop_data is thus unstable as a new requester with higher priority
// will preempt an existing requester.

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_mux_core #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = 1,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // Set to 1 if the arbiter is guaranteed to grant in a cycle when any request is asserted.
    parameter bit ArbiterAlwaysGrants = 1
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input  logic                           clk,                     // Used for assertions only
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input  logic                           rst,                     // Used for assertions only
    // Interface to base arbiter
    output logic [NumFlows-1:0]            request,
    input  logic [NumFlows-1:0]            can_grant,
    input  logic [NumFlows-1:0]            grant,
    output logic                           enable_priority_update,
    // External-facing signals
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    output logic                           pop_valid_unstable,
    output logic [   Width-1:0]            pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(numflows_gte_2_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  // This is a bit redundant with the integration checks in br_flow_arb_core,
  // but we need this to check data stability.
  // TODO(zhemao): Replace this with standalone data stability checks
  // so that we can reduce the redundant assertions.
  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------

  br_flow_arb_core #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .ArbiterAlwaysGrants(ArbiterAlwaysGrants)
  ) br_flow_arb_core (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
  );

  br_mux_onehot #(
      .NumSymbolsIn(NumFlows),
      .SymbolWidth (Width)
  ) br_mux_onehot (
      .select(grant),
      .in(push_data),
      .out(pop_data_unstable)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      // pop_data_unstable is unstable regardless of whether push_data is stable
      .EnableAssertDataStability(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data (pop_data_unstable)
  );

  for (genvar i = 0; i < NumFlows; i++) begin : gen_data_selected_assert
    `BR_ASSERT_IMPL(data_selected_when_granted_a,
                    (push_valid[i] && push_ready[i]) |-> pop_data_unstable == push_data[i])
  end
  // Additional implementation checks in submodules

endmodule : br_flow_mux_core
