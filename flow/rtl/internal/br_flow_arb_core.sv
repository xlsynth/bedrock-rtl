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

// Bedrock-RTL Flow-Controlled Arbiter Core
//
// This module is intended to work with one of the br_arb_* modules
// to implement a flow-controlled arbiter. Given two or more sets of
// ready-valid signals, it will arbitrate between them, granting one
// request per cycle if pop_ready is true.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_flow_arb_core #(
    // Must be at least 2
    parameter int NumFlows = 2,

    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable when backpressured.
    parameter bit EnableAssertPushValidStability = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // Set to 1 if the arbiter is not guaranteed to grant in a cycle when any request is
    // asserted.
    parameter bit ArbiterMayNotAlwaysGrant = 0
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input logic clk,  // Only used for assertions
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input logic rst,  // Only used for assertions
    // Interface to base arbiter
    output logic [NumFlows-1:0] request,
    input logic [NumFlows-1:0] can_grant,
    input logic [NumFlows-1:0] grant,
    output logic enable_priority_update,
    // External-facing signals
    output logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic pop_ready,
    output logic pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      // Data is always stable when valid is stable since it is constant.
      .EnableAssertDataStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({NumFlows{1'b0}})
  );

  // Internal integration checks
  `BR_ASSERT_IMPL(request_implies_grant_a, |request |-> ArbiterMayNotAlwaysGrant || (|grant))
  `BR_ASSERT_IMPL(grant_onehot0_a, $onehot0(grant))
  `BR_ASSERT_IMPL(grant_is_request_and_can_grant_a,
                  ArbiterMayNotAlwaysGrant || (grant == (request & can_grant)))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  assign request = push_valid;
  // only allow priority update if we actually grant
  assign enable_priority_update = pop_ready;
  assign push_ready = {NumFlows{pop_ready}} & can_grant;
  assign pop_valid_unstable = ArbiterMayNotAlwaysGrant ? |(push_valid & can_grant) : |push_valid;

  // grant is only used for assertions
  `BR_UNUSED(grant)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(1),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      // Data is always stable when valid is stable since it is constant.
      .EnableAssertDataStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data (1'b0)
  );

  `BR_ASSERT_IMPL(push_handshake_onehot0_a, $onehot0(push_valid & push_ready))
  `BR_ASSERT_IMPL(no_push_ready_without_pop_ready_a, (|push_ready) |-> pop_ready)
  `BR_ASSERT_IMPL(push_handshake_implies_pop_handshake_a,
                  |(push_valid & push_ready) |-> (pop_valid_unstable & pop_ready))
  for (genvar i = 0; i < NumFlows; i++) begin : gen_per_flow_impl_checks
    `BR_ASSERT_IMPL(only_accept_on_grant_a, (push_valid[i] & push_ready[i]) |-> grant[i])
  end

endmodule : br_flow_arb_core
