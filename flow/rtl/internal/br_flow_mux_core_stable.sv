// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Flow-Controlled Stable Multiplexer Core
//
// Combines core-priority arbitration with data path multiplexing.
// Grants a single request at a time with core priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop).
//
// Stateful arbiter and single-cycle latency from push to pop.
// A flow register is added to the output to ensure that the pop_data
// is stable.

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_flow_mux_core_stable #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, ensure that the pop ready signal is registered
    // at the input. This ensures there is no combinational path
    // from pop_ready to push_ready.
    parameter bit RegisterPopReady = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = 1,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
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
  // Rely on submodule integration checks


  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic internal_pop_valid;
  logic internal_pop_ready;
  logic [Width-1:0] internal_pop_data;

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready(internal_pop_ready),
      .pop_valid_unstable(internal_pop_valid),
      .pop_data_unstable(internal_pop_data)
  );

  if (RegisterPopReady) begin : gen_flow_reg_both
    br_flow_reg_both #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        // internal_pop_data cannot be stable
        .EnableAssertPushDataStability(0),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_both (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid),
        .push_data (internal_pop_data),
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end else begin : gen_flow_reg_fwd
    br_flow_reg_fwd #(
        .Width(Width),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        // internal_pop_data cannot be stable
        .EnableAssertPushDataStability(0),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid),
        .push_data (internal_pop_data),
        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  br_flow_checks_valid_data_impl #(
      .Width(Width),
      // The registered output will always be stable
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(1),
      .EnableAssertDataStability(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid),
      .data (pop_data)
  );

endmodule : br_flow_mux_core_stable
