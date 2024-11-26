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

// Bedrock-RTL Flow-Controlled Multiplexer Core
//
// Combines core-priority arbitration with data path multiplexing.
// Grants a single request at a time with core priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// Stateful arbiter, but 0 latency from push to pop.

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_mux_core #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1  // Must be at least 1
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input  logic                           clk,                     // Used for assertions only
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input  logic                           rst,                     // Used for assertions only
    // Interface to base arbiter
    output logic [NumFlows-1:0]            request,
    input  logic [NumFlows-1:0]            can_grant,
    input  logic [NumFlows-1:0]            grant,
    output logic                           enable_priority_update,
    // External-facing signals
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    output logic                           pop_valid,
    output logic [   Width-1:0]            pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(numflows_gte_2_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------

  br_flow_arb_core #(
      .NumFlows(NumFlows)
  ) br_flow_arb_core (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid
  );

  br_mux_onehot #(
      .NumSymbolsIn(NumFlows),
      .SymbolWidth (Width)
  ) br_mux_onehot (
      .select(grant),
      .in(push_data),
      .out(pop_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  for (genvar i = 0; i < NumFlows; i++) begin : gen_data_selected_assert
    `BR_ASSERT_IMPL(data_selected_when_granted_a,
                    (pop_valid && push_ready[i]) |-> pop_data == push_data[i])
  end
  // Additional implementation checks in submodules

endmodule : br_flow_mux_core
