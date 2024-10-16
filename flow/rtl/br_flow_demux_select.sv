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

// Bedrock-RTL Flow Demux with Select
//
// A dataflow pipeline demux with explicit select.
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

module br_flow_demux_select #(
    // Must be at least 2
    parameter int NumFlows = 2,
    // Must be at least 1
    parameter int BitWidth = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    input logic [$clog2(NumFlows)-1:0] select,

    output logic                push_ready,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    input  logic [NumFlows-1:0]               pop_ready,
    output logic [NumFlows-1:0]               pop_valid,
    output logic [NumFlows-1:0][BitWidth-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Register the push outputs to hide the delays of the combinational demuxing logic.
  // Note that there are still combinational paths from push_valid (and pop_data)
  // and select to pop_valid (and pop_data).

  logic internal_ready;
  logic internal_valid;
  logic [BitWidth-1:0] internal_data;

  br_flow_reg_rev #(
      .BitWidth(BitWidth)
  ) br_flow_reg_rev (
      .clk(clk),
      .rst(rst),
      .push_ready(push_ready),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(internal_ready),
      .pop_valid(internal_valid),
      .pop_data(internal_data)
  );

  br_flow_demux_select_unstable #(
      .NumFlows(NumFlows),
      .BitWidth(BitWidth)
  ) br_flow_demux_select_unstable (
      .clk(clk),
      .rst(rst),
      .select(select),
      .push_ready(internal_ready),
      .push_valid(internal_valid),
      .push_data(internal_data),
      .pop_ready(pop_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_demux_select
