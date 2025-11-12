// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Arbiter (Round-Robin)
//
// Grants a single request at a time with round-robin priority
// where the lowest index flow initializes with the highest priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// 0-cycle latency, but clock and reset are still needed to manage
// the internal arbiter priority state.
// Pop valid can be unstable if push valid is unstable and all active push_valid
// are withdrawn while pop_ready is low.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_flow_arb_rr #(
    // Must be at least 2
    parameter int NumFlows = 2,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,
    output logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic pop_ready,
    // Pop valid can be unstable if push valid is unstable
    // and all active push_valid are withdrawn while pop_ready is low
    output logic pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] can_grant;
  logic [NumFlows-1:0] grant;
  logic enable_priority_update;

  br_arb_rr_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .can_grant,
      .grant
  );

  br_flow_arb_core #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
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

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_arb_rr
