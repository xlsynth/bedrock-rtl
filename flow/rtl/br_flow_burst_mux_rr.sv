// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Burst Multiplexer (Round-Robin)
//
// Combines RR-priority arbitration with data path multiplexing.
// Grants a single request for a multi-cycle burst with RR priority.
// The granted channel will continue to be granted until it asserts push_last.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// Stateful arbiter, but 0 latency from push to pop.
// The pop data is thus unstable as a new requester with higher priority will
// preempt an existing requester. Pop valid can be unstable if all push valids
// are revoked while pop_ready is low.

`include "br_asserts.svh"

module br_flow_burst_mux_rr #(
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
    // Pop valid can be unstable if push valid is unstable
    // and all active push_valid are withdrawn while pop_ready is low
    output logic                           pop_valid_unstable,
    // Pop last will be unstable if a higher priority requester
    // asserts on push_valid while pop_ready is low
    output logic                           pop_last_unstable,
    // Pop data will be unstable if a higher priority requester
    // asserts on push_valid while pop_ready is low
    output logic [   Width-1:0]            pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_requesters_gte_1_a, NumFlows >= 1)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] can_grant;
  logic [NumFlows-1:0] grant;
  logic [NumFlows-1:0] grant_from_arb;
  logic [NumFlows-1:0] grant_hold;
  logic enable_priority_update;
  logic enable_grant_hold_update;
  logic enable_priority_update_from_mux;
  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload_unstable;

  assign can_grant = grant;
  assign grant_hold = ~(push_valid & push_last);
  assign enable_grant_hold_update = enable_priority_update_from_mux && |(grant & push_valid);

  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end

  br_arb_rr_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .request,
      .can_grant(),
      .grant(grant_from_arb),
      .enable_priority_update
  );

  br_arb_grant_hold #(
      .NumRequesters(NumFlows)
  ) br_arb_grant_hold (
      .clk,
      .rst,
      .grant_hold,
      .enable_grant_hold_update,
      .grant_from_arb,
      .enable_priority_update_to_arb(enable_priority_update),
      .grant
  );

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width + 1),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .ArbiterAlwaysGrants(0)
  ) br_flow_mux_core (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update(enable_priority_update_from_mux),
      .push_ready,
      .push_valid,
      .push_data(push_payload),
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable(pop_payload_unstable)
  );

  assign {pop_last_unstable, pop_data_unstable} = pop_payload_unstable;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_burst_mux_rr
