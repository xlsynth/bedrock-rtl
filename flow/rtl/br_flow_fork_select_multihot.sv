// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL Flow Fork With Multihot Select
//
// Forks a dataflow pipeline into a number of downstream pipelines.
// Only the selected pipelines are considered in flow control.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards. This module does not implement
// the datapath.

`include "br_asserts_internal.svh"

module br_flow_fork_select_multihot #(
    parameter int NumFlows = 2,  // Must be at least 2
    // If 1, cover that the select_multihot signal is multihot when valid is high.
    // If 0, assert that the select_multihot signal is always onehot when valid is high.
    parameter bit EnableCoverSelectMultihot = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that select_multihot is stable when backpressured.
    // If 0, cover that select_multihot can be unstable.
    parameter bit EnableAssertSelectMultihotStability = EnableAssertPushValidStability,
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
    input logic push_valid,
    input logic [NumFlows-1:0] push_select_multihot,  // pop-side selection, but qualified by push_valid

    // Pop-side interfaces
    //
    // pop_valid signals are unstable because they must fall if another selected pop_ready
    // falls, or a flow is unselected while backpressured.
    // There is no dependency between pop_valid_unstable[i] and pop_ready[i].
    input  logic [NumFlows-1:0] pop_ready,
    output logic [NumFlows-1:0] pop_valid_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_gte_2_a, NumFlows >= 2)

  `BR_ASSERT_INTG(select_not_0_when_valid_a, push_valid |-> (|select_multihot))
  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(NumFlows),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertSelectMultihotStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (select_multihot)
  );
  if (EnableCoverSelectMultihot) begin : gen_cover_select_multihot
    `BR_COVER_INTG(select_multihot_c, push_valid && !($onehot(select_multihot)))
  end else begin : gen_assert_onehot_select
    `BR_ASSERT_INTG(select_onehot_a, push_valid |-> $onehot(select_multihot))
  end
  `BR_ASSERT_INTG(select_multihot_known_a, push_valid |-> ($countones(select_multihot) > 1))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    push_ready = '1;
    for (int i = 0; i < NumFlows; i++) begin
      push_ready &= !select_multihot[i] || pop_ready[i];
    end
  end

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flows
    always_comb begin
      pop_valid_unstable[i] = push_valid && select_multihot[i];
      for (int j = 0; j < NumFlows; j++) begin
        // Keep valid if all other valid flows are ready
        if (i != j) begin
          pop_valid_unstable[i] &= !select_multihot[j] || pop_ready[j];
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
      .EnableCoverBackpressure(1),
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

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    `BR_COVER_IMPL(pop_valid_unstable_c, $stable(push_valid) && $fell(pop_valid_unstable[i]))
  end

endmodule : br_flow_fork_select_multihot
