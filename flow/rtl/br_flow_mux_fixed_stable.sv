// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Stable Multiplexer (Fixed-Priority)
//
// Combines fixed-priority arbitration with data path multiplexing.
// Grants a single request at a time with fixed (strict) priority
// where the lowest index flow has the highest priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop). Adds a flow register to the output to ensure
// that the pop_data is stable.
//
// Single-cycle latency from push to pop.

`include "br_asserts.svh"

module br_flow_mux_fixed_stable #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, ensure that the pop ready signal is registered
    // at the input. This ensures there is no combinational path
    // from pop_ready to push_ready.
    parameter bit RegisterPopReady = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input  logic                           clk,
    input  logic                           rst,
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    output logic                           pop_valid,
    output logic [   Width-1:0]            pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_requesters_gte_2_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] can_grant;
  logic [NumFlows-1:0] grant;

  br_arb_fixed_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_fixed_internal (
      .request,
      .can_grant,
      .grant
  );

  br_flow_mux_core_stable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .RegisterPopReady(RegisterPopReady),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core_stable (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update(),  // Not used
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_fixed_stable
