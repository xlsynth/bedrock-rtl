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

// Bedrock-RTL Flow Demux with Select
//
// A dataflow pipeline demux with explicit binary select.
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

module br_flow_demux_select #(
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
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    input logic [$clog2(NumFlows)-1:0] select,

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic [NumFlows-1:0]            pop_ready,
    output logic [NumFlows-1:0]            pop_valid,
    output logic [NumFlows-1:0][Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] internal_ready;
  logic [NumFlows-1:0] internal_valid_unstable;
  logic [NumFlows-1:0][Width-1:0] internal_data_unstable;

  br_flow_demux_select_unstable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_demux_select_unstable (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready(internal_ready),
      .pop_valid_unstable(internal_valid_unstable),
      .pop_data_unstable(internal_data_unstable)
  );

  // Register the pop outputs to hide the internal instability of the combinational demux.
  // There are still combinational paths from pop_ready to push_ready.
  for (genvar i = 0; i < NumFlows; i++) begin : gen_pop_reg
    br_flow_reg_fwd #(
        .Width(Width),
        // We know that valid and data can be unstable internally.
        // This register hides that instability from the pop interface.
        .EnableAssertPushValidStability(0),
        .EnableAssertPushDataStability(0),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_ready[i]),
        .push_valid(internal_valid_unstable[i]),
        .push_data (internal_data_unstable[i]),
        .pop_ready (pop_ready[i]),
        .pop_valid (pop_valid[i]),
        .pop_data  (pop_data[i])
    );
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_demux_select
