// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Lockstep Flow Join
//
// Joins a number of upstream dataflow pipelines that are in lockstep with each
// other into a single downstream pipeline. Lockstep means that push_valid[i] ==
// push_valid[j] for all combinations i and j. Uses the AMBA-inspired
// ready-valid handshake protocol for synchronizing pipeline stages and stalling
// when encountering backpressure hazards. This module does not implement the
// datapath.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_flow_join_lockstep #(
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
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Synchronous active-high reset. Used only for assertions.

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
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte1_a, NumFlows >= 1)

  `BR_ASSERT_INTG(push_valid_lockstep_a, (push_valid == {NumFlows{push_valid[0]}}))

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      // Data is always stable when valid is since it is constant.
      .EnableAssertDataStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data ({NumFlows{1'b0}})
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // The push_valid signals are all identical, so just pass the first bit through
  assign pop_valid  = push_valid[0];
  // Replicate the pop_ready signal to all push_ready signals.
  assign push_ready = {NumFlows{pop_ready}};

  if (NumFlows > 1) begin : gen_ignore_push_valid_msbs
    // Ignore all the push_valid bits other than the LSB
    `BR_UNUSED_NAMED(push_valid_msbs, push_valid[NumFlows-1:1])
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // The control flow behavior should be the same on pop as on push
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data (1'b0)
  );
endmodule
