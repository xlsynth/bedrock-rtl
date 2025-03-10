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

// Bedrock-RTL Flow-Controlled Crossbar (Least-Recently Used Arbitration)
//
// Implements a many-to-many crossbar with input and output ports
// all being ready/valid interfaces. Each input flow provides the data
// to be transferred and a destination ID, which is the binary encoded
// number corresponding to the desired output flow.
//
// This is a full crossbar with maximum throughput of min(NumPushFlows, NumPopFlows)
// transfers per cycle. Every input transaction can be accepted if they are all
// going to distinct destinations.
//
// Uses least-recently used (LRU) arbitration to grant requests.

module br_flow_xbar_lru #(
    // The number of input flows. Must be >=2.
    parameter int NumPushFlows = 2,
    // The number of output flows. Must be >=2.
    parameter int NumPopFlows = 2,
    // The width of the data bus.
    parameter int Width = 1,
    // If 1, registers are inserted between the demux and mux to break up the
    // timing path, increasing the cut-through latency by 1. Note that this
    // results in NumPushFlows x NumPopFlows x Width bits of registers being
    // inserted.
    parameter bit RegisterDemuxOutputs = 0,
    // If 1, registers are inserted at the output of the muxes, ensuring that
    // pop_valid/pop_data come directly from registers.
    // If 0, pop_valid/pop_data come directly from the muxes and may be unstable.
    parameter bit RegisterPopOutputs = 0,
    // If 1, cover that the push_ready signal can be backpressured.
    // If 0, assert that push backpressure is not possible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable.
    // Otherwise, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable.
    // Otherwise, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_valid is 1 and all intermediate
    // register stages are empty at end of simulation.
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int DestIdWidth = $clog2(NumPopFlows)
) (
    input logic clk,
    input logic rst,

    output logic [NumPushFlows-1:0] push_ready,
    input logic [NumPushFlows-1:0] push_valid,
    input logic [NumPushFlows-1:0][Width-1:0] push_data,
    input logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id,

    input logic [NumPopFlows-1:0] pop_ready,
    output logic [NumPopFlows-1:0] pop_valid,
    output logic [NumPopFlows-1:0][Width-1:0] pop_data
);

  //------------------------------------------
  // Integration Assertions
  //------------------------------------------
  // Rely on assertions in submodules

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [NumPopFlows-1:0][NumPushFlows-1:0] request;
  logic [NumPopFlows-1:0][NumPushFlows-1:0] can_grant;
  logic [NumPopFlows-1:0][NumPushFlows-1:0] grant;
  logic [NumPopFlows-1:0] enable_priority_update;

  br_flow_xbar_core #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width),
      .RegisterDemuxOutputs(RegisterDemuxOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_xbar_core_inst (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update
  );

  for (genvar i = 0; i < NumPopFlows; i++) begin : gen_arbiters
    br_arb_lru_internal #(
        .NumRequesters(NumPushFlows)
    ) br_arb_lru_internal_inst (
        .clk,
        .rst,
        .request(request[i]),
        .can_grant(can_grant[i]),
        .grant(grant[i]),
        .enable_priority_update(enable_priority_update[i])
    );
  end

endmodule
