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

// Basic checker of br_flow_arb

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_arb_basic_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure
) (
    input logic                clk,
    input logic                rst,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic                pop_ready,
    input logic                pop_valid_unstable
);

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))

  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    if (EnableAssertPushValidStability) begin : gen_push_valid
      `BR_ASSUME(push_valid_stable_a, push_valid[n] && !push_ready[n] |=> push_valid[n])
    end
  end

  // ----------Sanity Check----------
  if (EnableAssertPushValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid_unstable && !pop_ready |=> pop_valid_unstable)
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |push_valid == pop_valid_unstable)

  // ----------Critical Covers----------
  `BR_COVER(all_push_valid_c, &push_valid)

endmodule : br_flow_arb_basic_fpv_monitor
