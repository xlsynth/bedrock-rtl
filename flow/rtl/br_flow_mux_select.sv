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

// Bedrock-RTL Flow Mux with Select
//
// A dataflow pipeline mux with explicit select.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// TODO(mgottscho): Write spec doc

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_flow_mux_select #(
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
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    input logic [$clog2(NumFlows)-1:0] select,

    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Register the pop outputs to hide the delays of the combinational muxing logic.
  // Note that there are still combinational paths from pop_ready and select to push_ready.

  logic internal_ready;
  logic internal_valid;
  logic [Width-1:0] internal_data;

  br_flow_mux_select_unstable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) br_flow_mux_select_unstable (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready         (internal_ready),
      .pop_valid_unstable(internal_valid),
      .pop_data_unstable (internal_data)
  );

  br_flow_reg_fwd #(
      .Width(Width)
  ) br_flow_reg_fwd (
      .clk,
      .rst,
      .push_ready(internal_ready),
      .push_valid(internal_valid),
      .push_data (internal_data),
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_select
