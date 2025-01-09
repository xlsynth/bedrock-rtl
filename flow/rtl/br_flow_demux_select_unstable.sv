// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Flow Demux with Select
//
// A dataflow pipeline demux with explicit select.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// This is a purely combinational module with 0 delay.
//
// TODO(mgottscho): Write spec doc

`include "br_asserts_internal.svh"

module br_flow_demux_select_unstable #(
    // Must be at least 2
    parameter int NumFlows = 2,
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int SelectWidth = $clog2(NumFlows)
) (
    // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input logic [SelectWidth-1:0] select,

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic [NumFlows-1:0]            pop_ready,
    output logic [NumFlows-1:0]            pop_valid,
    output logic [NumFlows-1:0][Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_must_be_at_least_two_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  br_flow_checks_valid_data #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability)
  ) br_flow_checks_valid_data (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  if (EnableCoverPushBackpressure && EnableAssertPushValidStability)
  begin : gen_select_stability_check
    // If push_valid is backpressured, the select must be stable
    // to maintain valid stability on the pop side.
    `BR_ASSERT_INTG(select_stability_a, (push_valid && !push_ready) |=> $stable(select))
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Lint waivers are safe because we assert select is always in range.
  // ri lint_check_waive VAR_INDEX_READ
  assign push_ready = pop_ready[select];
  // ri lint_check_waive VAR_SHIFT TRUNC_LSHIFT
  assign pop_valid = push_valid ? (push_valid << select) : '0;
  // Replicate pop_data to all flows; this is okay since pop_data[i]
  // is only valid when pop_valid[i] is high.
  always_comb begin
    for (int i = 0; i < NumFlows; i++) begin
      pop_data[i] = push_data;
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // TODO(mgottscho): Add implementation checks on ready-valid compliance.

endmodule : br_flow_demux_select_unstable
