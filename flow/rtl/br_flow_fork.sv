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
    parameter int NumFlows = 2,  // Must be at least 2
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
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
  `BR_ASSERT_STATIC(num_flows_gte_2_a, NumFlows >= 2)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
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
      .data (1'b0)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign push_ready = &pop_ready;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flows
    always_comb begin
      pop_valid_unstable[i] = push_valid;
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          pop_valid_unstable[i] &= pop_ready[j];
        end
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      // We know that the pop valids can be unstable.
      .EnableAssertValidStability(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data ({NumFlows{1'b0}})
  );

  if (EnableCoverPushBackpressure) begin : gen_push_backpressure_cover
    `BR_COVER_IMPL(pop_valid_unstable_c, !$stable(pop_valid_unstable))
  end

endmodule : br_flow_fork
