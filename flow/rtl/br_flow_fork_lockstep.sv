// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Lockstep Flow Fork
//
// Forks a dataflow pipeline into a number of downstream pipelines
// that always accept or backpressure in lockstep with each other.
// That is, pop_ready[i] == pop_ready[j] for all i, j.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards. This module does not implement
// the datapath.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_flow_fork_lockstep #(
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
    input  logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0] pop_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte_1_a, NumFlows >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (1'b0)
  );

  `BR_ASSERT_INTG(pop_ready_lockstep_a, (pop_ready == {NumFlows{pop_ready[0]}}))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Replicate the push_valid to all pop_valid bits
  assign pop_valid  = {NumFlows{push_valid}};
  // Since pop_ready bits are identical, we can just pass on the LSB and ignore the other bits.
  assign push_ready = pop_ready[0];
  if (NumFlows > 1) begin : gen_ignore_pop_ready_msbs
    `BR_UNUSED_NAMED(pop_ready_msbs, pop_ready[NumFlows-1:1])
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data ({NumFlows{1'b0}})
  );

endmodule : br_flow_fork_lockstep
