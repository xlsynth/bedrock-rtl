// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Fork With Unstable Push
//
// A flow fork that accepts valid which may change or be revoked while
// push_ready is low. The fork remains purely combinational, so each pop valid
// is also explicitly unstable while any other pop flow is backpressured.

`include "br_asserts.svh"

module br_flow_fork_unstable #(
    // Must be at least 1
    parameter int NumFlows = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input  logic                clk,
    input  logic                rst,
    output logic                push_ready,
    input  logic                push_valid_unstable,
    input  logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0] pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte_1_a, NumFlows >= 1)

  // Rely on submodule integration checks.

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // The fork accepts only ready/valid transfers. Disable its push-side valid
  // stability check because instability is this wrapper's contract.
  br_flow_fork #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(1'b0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) br_flow_fork (
      .clk,
      .rst,
      .push_ready,
      .push_valid(push_valid_unstable),
      .pop_ready,
      .pop_valid_unstable
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks.

endmodule : br_flow_fork_unstable
