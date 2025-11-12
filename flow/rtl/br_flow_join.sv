// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Join
//
// Joins a number of upstream dataflow pipelines into a single downstream
// pipeline. Uses the AMBA-inspired ready-valid handshake protocol for
// synchronizing pipeline stages and stalling when encountering backpressure
// hazards. This module does not implement the datapath.

`include "br_asserts_internal.svh"

module br_flow_join #(
    parameter int NumFlows = 2,  // Must be at least 2
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
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
  `BR_ASSERT_STATIC(num_flows_gte2_a, NumFlows >= 2)


  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
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
  for (genvar i = 0; i < NumFlows; i++) begin : gen_flows
    always_comb begin
      push_ready[i] = pop_ready;
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          push_ready[i] &= push_valid[j];
        end
      end
    end
  end

  assign pop_valid = &push_valid;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(1),
      .EnableCoverBackpressure(1),
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

endmodule : br_flow_join
