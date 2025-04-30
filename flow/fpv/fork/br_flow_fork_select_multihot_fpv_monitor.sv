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

`include "br_asserts.svh"

module br_flow_fork_select_multihot_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter bit EnableCoverSelectMultihot = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertSelectMultihotStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic push_ready,
    input logic push_valid,
    input logic [NumFlows-1:0] push_select_multihot,

    // Pop-side interfaces
    // pop_valid signals are unstable because they must fall if another pop_ready falls.
    // There is no dependency between pop_valid[i] and pop_ready[i].
    input logic [NumFlows-1:0] pop_ready,
    input logic [NumFlows-1:0] pop_valid_unstable
);

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready[n]))
  end

  if (EnableAssertPushValidStability) begin : gen_push_valid
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertSelectMultihotStability) begin : gen_data
    `BR_ASSUME(multihot_stable_a, push_valid && !push_ready |=> $stable(push_select_multihot))
  end

  if (!EnableCoverSelectMultihot) begin : gen_1hot
    `BR_ASSUME(select_onehot_a, push_valid |-> $onehot(push_select_multihot))
  end
  `BR_ASSUME(legal_select_a, push_valid |-> |push_select_multihot)

  // ----------FV assertions----------
  // pick a random constant for assertion
  logic [$clog2(NumFlows)-1:0] fv_idx;
  `BR_ASSUME(fv_idx_a, $stable(fv_idx) && fv_idx < NumFlows)

  `BR_ASSERT(
      forward_progress_a,
      push_valid && push_ready && push_select_multihot[fv_idx] |-> pop_valid_unstable[fv_idx])

endmodule : br_flow_fork_select_multihot_fpv_monitor

bind br_flow_fork_select_multihot br_flow_fork_select_multihot_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverSelectMultihot(EnableCoverSelectMultihot),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertSelectMultihotStability(EnableAssertSelectMultihotStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
