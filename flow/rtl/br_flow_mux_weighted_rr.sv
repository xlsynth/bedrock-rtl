// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Multiplexer (Weighted Round-Robin)
//
// Combines weighted round-robin (WRR) arbitration with data path multiplexing.
// Grants a single request at a time with WRR priority.
// Uses ready-valid flow control for flows (push) and the grant (pop).
//
// Stateful arbiter, but 0 latency from push to pop.
// The pop data is thus unstable as a new requester with higher priority will
// preempt an existing requester. Pop valid can be unstable if all push valids
// are revoked while pop_ready is low.
//
// `cfg_weight` is the arbiter weight for each flow. They are expected to follow the rules
// set for `request_weight` in `br_arb_weighted_rr`. Weights cannot be zero and are expected
// to be stable while traffic is ongoing.

`include "br_asserts.svh"

module br_flow_mux_weighted_rr #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    // Must be at least 1
    parameter int MaxWeight = 1,
    // Maximum accumulated weight per requester. Must be at least MaxWeight.
    parameter int MaxAccumulatedWeight = MaxWeight,
    // If 1, use pairwise grant selection instead of unrolled grant selection. Pairwise grant
    // selection can provide better PPA for small requester counts, but its O(N^2) priority
    // matrix scales worse than the unrolled implementation as the requester count grows.
    // The two implementations are functionally equivalent.
    parameter bit UsePairwiseArb = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    localparam int WeightWidth = $clog2(MaxWeight + 1)
) (
    input  logic                                 clk,
    input  logic                                 rst,
    input  logic [NumFlows-1:0][WeightWidth-1:0] cfg_weight,
    output logic [NumFlows-1:0]                  push_ready,
    input  logic [NumFlows-1:0]                  push_valid,
    input  logic [NumFlows-1:0][      Width-1:0] push_data,
    input  logic                                 pop_ready,
    // Pop valid can be unstable if push valid is unstable
    // and all active push_valid are withdrawn while pop_ready is low
    output logic                                 pop_valid_unstable,
    // Pop data will be unstable if a higher priority requester
    // asserts on push_valid while pop_ready is low
    output logic [   Width-1:0]                  pop_data_unstable
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
  logic [NumFlows-1:0] grant;
  logic enable_priority_update;

  br_arb_weighted_rr #(
      .NumRequesters(NumFlows),
      .MaxWeight(MaxWeight),
      .MaxAccumulatedWeight(MaxAccumulatedWeight),
      .UsePairwiseArb(UsePairwiseArb)
  ) br_arb_weighted_rr_inst (
      .clk,
      .rst,
      .request,
      .request_weight(cfg_weight),
      .grant,
      .enable_priority_update
  );

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core (
      .clk,
      .rst,
      .request,
      .can_grant(grant),
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_weighted_rr
