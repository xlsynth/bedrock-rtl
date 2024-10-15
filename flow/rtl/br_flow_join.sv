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

// Bedrock-RTL Flow Join
//
// Joins a number of upstream dataflow pipelines into a single downstream
// pipeline. Uses the AMBA-inspired ready-valid handshake protocol for
// synchronizing pipeline stages and stalling when encountering backpressure
// hazards. This module does not implement the datapath.

`include "br_asserts_internal.svh"

module br_flow_join #(
    parameter int NumFlows = 2  // Must be at least 2
) (
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Used only for assertions

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

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    `BR_ASSERT_INTG(push_valid_stable_A, !push_ready[i] && push_valid[i] |=> push_valid[i])
  end

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
  `BR_ASSERT_IMPL(pop_backpressure_a, !pop_ready && pop_valid |=> pop_valid)

endmodule : br_flow_join
