// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Join
//
// Joins a number of upstream dataflow pipelines into a single downstream
// pipeline. Uses the AMBA-inspired ready-valid handshake protocol for
// synchronizing pipeline stages and stalling when encountering backpressure
// hazards. This module does not implement the datapath.

`include "br_asserts_internal.svh"

module br_flow_join #(
    parameter int NumFlows = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    // Push-side interfaces
    output logic [NumFlows-1:0] push_ready,
    input  logic [NumFlows-1:0] push_valid,

    // Pop-side interface
    input  logic pop_ready,
    output logic pop_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on checks in submodule

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_flow_join_select_multihot #(
      .NumFlows(NumFlows),
      .AllowEmptySelect(0),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) br_flow_join_select_multihot (
      .clk,
      .rst,
      .select_multihot('1),  // All flows always selected
      .push_ready,
      .push_valid,
      .pop_ready,
      // Since select is always one, the pop_valid will be stable
      .pop_valid_unstable(pop_valid)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Checks in submodule
endmodule : br_flow_join
