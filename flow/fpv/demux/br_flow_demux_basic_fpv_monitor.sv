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

// Basic checker of br_flow_demux

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_demux_basic_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability
) (
    input logic                                   clk,
    input logic                                   rst,
    input logic [$clog2(NumFlows)-1:0]            select,
    input logic                                   push_ready,
    input logic                                   push_valid,
    input logic [           Width-1:0]            push_data,
    input logic [        NumFlows-1:0]            pop_ready,
    input logic [        NumFlows-1:0]            pop_valid,
    input logic [        NumFlows-1:0][Width-1:0] pop_data
);

  // pick a random constant for assertion
  logic [$clog2(NumFlows)-1:0] fv_idx;
  `BR_ASSUME(fv_idx_a, $stable(fv_idx) && fv_idx < NumFlows)

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready[n]))
  end

  if (EnableAssertPushValidStability) begin : gen_push_valid
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data
    `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data))
  end

  // ----------Sanity Check----------
  if (EnableAssertPushValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid[fv_idx] && !pop_ready[fv_idx] |=> pop_valid[fv_idx])
  end
  if (EnableAssertPushDataStability) begin : gen_pop_data
    `BR_ASSERT(pop_data_stable_a,
               pop_valid[fv_idx] && !pop_ready[fv_idx] |=> $stable(pop_data[fv_idx]))
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, push_valid |-> pop_valid[select])

endmodule : br_flow_demux_basic_fpv_monitor
