// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Valve
//
// Gates a set of data-less ready-valid flows with an enable signal. Uses the
// AMBA-inspired ready-valid handshake protocol for synchronizing pipeline
// stages and stalling when encountering backpressure hazards.

`include "br_asserts_internal.svh"

module br_flow_valve #(
    parameter int NumFlows = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, then assert there are no push-valid bits asserted at the end of the test.
    parameter bit EnableAssertPushFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    // If 1, assert that pop-side backpressure is impossible.
    parameter bit EnableAssertNoPopBackpressure = 0
) (
    // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input logic [NumFlows-1:0] en,

    // Push-side interfaces
    output logic [NumFlows-1:0] push_ready,
    input  logic [NumFlows-1:0] push_valid,

    // Pop-side interfaces
    //
    // pop_valid_unstable can be unstable because it falls if en falls.
    input  logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0] pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte_1_a, NumFlows >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(0),
      .EnableAssertFinalNotValid(EnableAssertPushFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ('0)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign push_ready         = pop_ready & en;
  assign pop_valid_unstable = push_valid & en;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(0),
      .EnableAssertNoBackpressure(EnableAssertNoPopBackpressure),
      .EnableAssertValidStability(0),
      .EnableAssertFinalNotValid(0)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data ('0)
  );

endmodule : br_flow_valve
