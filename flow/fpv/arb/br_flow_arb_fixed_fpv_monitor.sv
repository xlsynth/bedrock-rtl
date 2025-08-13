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

// Bedrock-RTL Flow-Controlled Arbiter (Fixed-Priority) FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_arb_fixed_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                clk,
    input logic                rst,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic                pop_ready,
    input logic                pop_valid_unstable,
    // RTL internal signal
    input logic [NumFlows-1:0] grant
);

  // ----------Instantiate basic checks----------
  br_flow_arb_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
  );

  // ----------FV Modeling Code----------
  logic [$clog2(NumFlows)-1:0] i, j;
  `BR_FV_2RAND_IDX(i, j, NumFlows)

  // ----------Fairness Check----------
  if (EnableCoverPushBackpressure) begin : gen_strict_priority_check
    `BR_ASSERT(strict_priority_a, (i < j) && push_valid[i] && push_valid[j] |-> !grant[j])
  end

endmodule : br_flow_arb_fixed_fpv_monitor

bind br_flow_arb_fixed br_flow_arb_fixed_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
