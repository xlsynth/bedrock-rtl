// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Burst Multiplexer (Fixed-Priority)
//
// Combines fixed-priority arbitration with data path multiplexing.
// Grants a single request for a multi-cycle burst with fixed (strict) priority
// where the lowest index flow has the highest priority.
// The granted channel will continue to be granted until it asserts push_last
// alongside push_valid.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// Purely combinational from push to pop, with state only for burst ownership.
//
// Pop data / last are unstable because a new higher-priority requester can preempt
// before a burst has been captured, and pop_valid can be unstable if all push valids
// are revoked while pop_ready is low.

`include "br_asserts.svh"

module br_flow_burst_mux_fixed #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input  logic                           clk,
    input  logic                           rst,
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0]            push_last,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    output logic                           pop_valid_unstable,
    output logic                           pop_last_unstable,
    output logic [   Width-1:0]            pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_requesters_gte_1_a, NumFlows >= 1)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] grant_from_arb;

  br_arb_fixed_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_fixed_internal (
      .request,
      .can_grant(),
      .grant(grant_from_arb)
  );

  br_flow_burst_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_burst_mux_core (
      .clk,
      .rst,
      .request,
      .grant_from_arb,
      .enable_priority_update(),
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready,
      .pop_valid_unstable,
      .pop_last_unstable,
      .pop_data_unstable
  );

endmodule : br_flow_burst_mux_fixed
