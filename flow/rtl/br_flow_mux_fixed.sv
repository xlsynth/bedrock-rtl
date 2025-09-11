// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

module br_flow_mux_fixed #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                           clk,                 // Only used for assertions
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                           rst,                 // Only used for assertions
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    // Pop valid can be unstable if push valid is unstable
    // and all active push_valid are withdrawn while pop_ready is low
    output logic                           pop_valid_unstable,
    // Pop data will be unstable if a higher priority requester
    // asserts on push_valid while pop_ready is low
    output logic [   Width-1:0]            pop_data_unstable
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

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core (
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
      .pop_valid_unstable,
      .pop_data_unstable
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_fixed
