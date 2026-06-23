// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Fork
//
// Forks a dataflow pipeline into a number of downstream pipelines.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards. This module does not implement
// the datapath.

`include "br_asserts_internal.svh"

module br_flow_fork #(
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
    // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    // Push-side interface
    output logic push_ready,
    input  logic push_valid,

    // Pop-side interfaces
    //
    // pop_valid signals are unstable because they must fall if another pop_ready falls.
    // There is no dependency between pop_valid[i] and pop_ready[i].
    input  logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0] pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on checks in submodule

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_flow_fork_select_multihot #(
      .NumFlows(NumFlows),
      .EnableCoverSelectMultihot(1),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertSelectMultihotStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) br_flow_fork_select_multihot (
      .clk,
      .rst,
      .push_ready(push_ready),
      .push_valid(push_valid),
      .push_select_multihot('1),
      .pop_ready(pop_ready),
      .pop_valid_unstable(pop_valid_unstable)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on checks in submodule

endmodule : br_flow_fork
