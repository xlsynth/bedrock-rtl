// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Join Select Multihot
//
// Selectively joins a number of upstream dataflow pipelines into a single
// downstream pipeline. Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when encountering backpressure
// hazards. Only the flows for that are selected will participate in the handshake.
// The unselected flows will not have their push_ready asserted and will not
// block assertion of pop_valid. This module does not implement the datapath.
// If select_multihot is all zeros, pop_valid will not be asserted.

`include "br_asserts_internal.svh"

module br_flow_join_select_multihot #(
    parameter int NumFlows = 1,  // Must be at least 1
    // If 1, select_multihot could be zero, and extra logic will be inserted
    // to ensure there is no pop handshake in that case.
    // If 0, select_multihot must have at least one bit set, and this additional
    // logic will be omitted.
    parameter bit AllowEmptySelect = 1,
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

    // Unqualified multihot select of push flows
    input logic [NumFlows-1:0] select_multihot,

    // Push-side interfaces
    output logic [NumFlows-1:0] push_ready,
    input  logic [NumFlows-1:0] push_valid,

    // Pop-side interface
    input  logic pop_ready,
    // Valid could be unstable if select_multihot changes while pop side is backpressured.
    // TODO(zhemao): Figure out the right way to constraint the input to avoid this.
    output logic pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte1_a, NumFlows >= 1)
  `BR_ASSERT_KNOWN(select_multihot_known_a, select_multihot)
  if (AllowEmptySelect) begin : gen_cover_empty_select
    `BR_COVER_INTG(empty_select_c, select_multihot == '0)
  end else begin : gen_assert_nonempty_select
    `BR_ASSERT_INTG(select_nonempty_a, select_multihot != '0)
  end

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
  logic [NumFlows-1:0] push_valid_or_unselected;

  assign push_valid_or_unselected = push_valid | ~select_multihot;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flows
    always_comb begin
      push_ready[i] = pop_ready && select_multihot[i];
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          push_ready[i] &= push_valid_or_unselected[j];
        end
      end
    end
  end

  if (AllowEmptySelect) begin : gen_empty_select_pop_valid
    assign pop_valid_unstable = (|push_valid) && (&push_valid_or_unselected);
  end else begin : gen_non_empty_select_pop_valid
    assign pop_valid_unstable = &push_valid_or_unselected;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      // TODO(zhemao): Pass parameters for select_multihot constraints that make pop_valid stable
      .EnableAssertValidStability(0),
      .EnableAssertDataStability(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data (1'b0)
  );

endmodule : br_flow_join_select_multihot
