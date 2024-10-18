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

// Bedrock-RTL Flow Fork
//
// Forks a dataflow pipeline into a number of downstream pipelines.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards. This module does not implement
// the datapath.

`include "br_asserts_internal.svh"

module br_flow_fork #(
    parameter int NumFlows = 2  // Must be at least 2
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
  `BR_ASSERT_INTG(push_backpressure_a, !push_ready && push_valid |=> push_valid)

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
  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    `BR_COVER_IMPL(pop_valid_unstable_c, $stable(push_valid) && $fell(pop_valid_unstable[i]))
  end

endmodule : br_flow_fork
