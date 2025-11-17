// SPDX-License-Identifier: Apache-2.0


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
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, cover that the pop side experiences backpressure.
    // If 0, assert that there is never pop backpressure.
    parameter bit EnableCoverPopBackpressure = EnableCoverPushBackpressure,
    // Set to 1 if the arbiter is guaranteed to grant in a cycle when any request is asserted.
    parameter bit ArbiterAlwaysGrants = 1
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
      .EnableAssertValidStability(0),
      .EnableAssertDataStability(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({NumFlows{1'b0}})
  );

  // Internal integration checks
  if (ArbiterAlwaysGrants) begin : gen_arbiter_always_grants_asserts
    `BR_ASSERT_IMPL(request_implies_grant_a, |request |-> |grant)
    `BR_ASSERT_IMPL(grant_is_request_and_can_grant_a, grant == (request & can_grant))
  end
  `BR_ASSERT_IMPL(grant_onehot0_a, $onehot0(grant))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  assign request = push_valid;
  // only allow priority update if we actually grant
  assign enable_priority_update = pop_ready;
  assign push_ready = {NumFlows{pop_ready}} & can_grant;
  if (ArbiterAlwaysGrants) begin : gen_arbiter_always_grants
    assign pop_valid_unstable = |push_valid;
  end else begin : gen_arbiter_may_not_always_grant
    assign pop_valid_unstable = |(push_valid & can_grant);
  end

  // grant is only used for assertions
  `BR_UNUSED(grant)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(1),
      // Since push_ready can only be true if pop_ready is,
      // pop side can only have backpressure if push side has backpressure.
      .EnableCoverBackpressure(EnableCoverPopBackpressure),
      .EnableAssertValidStability(0),
      .EnableAssertDataStability(0),
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
    if (EnableCoverPopBackpressure) begin : gen_cover_pop_unstable
      `BR_COVER_IMPL(pop_unstable_c,
                     !pop_ready && pop_valid_unstable ##1 !$stable(pop_valid_unstable))
    end
  end

endmodule : br_flow_arb_core
