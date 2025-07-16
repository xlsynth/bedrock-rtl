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

// Bedrock-RTL Flow-Controlled Stable Multiplexer (Round-Robin)
//
// Combines round-robin arbitration with data path multiplexing.
// Grants a single request at a time with round-robin priority.
// Uses ready-valid flow control for flows (push)
// and the grant (pop). Adds a flow register to the output to ensure
// that the pop_data is stable.
//
// Single-cycle latency from push to pop.

`include "br_asserts.svh"

module br_flow_mux_rr_stable #(
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
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input  logic                           clk,
    input  logic                           rst,
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
  `BR_ASSERT_STATIC(num_requesters_gte_2_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] request;
  logic [NumFlows-1:0] can_grant;
  logic [NumFlows-1:0] grant;
  logic enable_priority_update;

  br_arb_rr_internal #(
      .NumRequesters(NumFlows)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update
  );

  br_flow_mux_core_stable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .RegisterPopReady(RegisterPopReady),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_core_stable (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_rr_stable
