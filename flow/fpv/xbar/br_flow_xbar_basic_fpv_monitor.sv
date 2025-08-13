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

// Basic checker of br_flow_reg

`include "br_asserts.svh"
`include "br_registers.svh"

module br_flow_xbar_basic_fpv_monitor #(
    parameter int NumPushFlows = 2,
    parameter int NumPopFlows = 2,
    parameter int Width = 1,
    parameter bit RegisterDemuxOutputs = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDestinationStability = EnableAssertPushValidStability,
    localparam int PushDestIdWidth = $clog2(NumPushFlows),
    localparam int DestIdWidth = $clog2(NumPopFlows)
) (
    input logic clk,
    input logic rst,

    input logic [NumPushFlows-1:0] push_ready,
    input logic [NumPushFlows-1:0] push_valid,
    input logic [NumPushFlows-1:0][Width-1:0] push_data,
    input logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id,

    input logic [NumPopFlows-1:0] pop_ready,
    input logic [NumPopFlows-1:0] pop_valid,
    input logic [NumPopFlows-1:0][Width-1:0] pop_data,

    input logic [PushDestIdWidth-1:0] fv_push_id,
    input logic [DestIdWidth-1:0] fv_pop_id
);

  localparam int Latency = RegisterDemuxOutputs + RegisterPopOutputs;
  // when push_valid & push_ready from fv_push_id are sending to fv_pop_id
  logic fv_push_vr;
  logic fv_pop_vr;

  assign fv_push_vr = push_valid[fv_push_id] && push_ready[fv_push_id]
                      && (push_dest_id[fv_push_id] == fv_pop_id);
  assign fv_pop_vr = pop_valid[fv_pop_id] && pop_ready[fv_pop_id]
                     && (pop_data[fv_pop_id][PushDestIdWidth-1:0] == fv_push_id);

  // ----------FV assumptions----------
  for (genvar i = 0; i < NumPushFlows; i++) begin : gen_push
    `BR_ASSUME(push_dest_id_legal_a, push_valid[i] |-> push_dest_id[i] < NumPopFlows)
    // color lower bits of push_data from each push port
    // e.g: if NumPushFlows = 4:
    // push_data[0][1:0] == 2'b00
    // push_data[1][1:0] == 2'b01
    // push_data[2][1:0] == 2'b10
    // push_data[3][1:0] == 2'b11
    // but higher bits can be random value
    `BR_ASSUME(color_push_data_a, push_valid[i] |-> push_data[i][PushDestIdWidth-1:0] == i)
    if (EnableCoverPushBackpressure) begin : gen_push_backpressure
      if (EnableAssertPushValidStability) begin : gen_push_valid
        `BR_ASSUME(push_valid_stable_a, push_valid[i] && !push_ready[i] |=> push_valid[i])
      end
      if (EnableAssertPushDataStability) begin : gen_push_data
        `BR_ASSUME(push_data_stable_a, push_valid[i] && !push_ready[i] |=> $stable(push_data[i]))
      end
      if (EnableAssertPushDestinationStability) begin : gen_push_dest_id
        `BR_ASSUME(push_dest_id_stable_a,
                   push_valid[i] && !push_ready[i] |=> $stable(push_dest_id[i]))
      end
    end else begin : gen_no_push_backpressure
      `BR_ASSUME(no_backpressure_a, !push_ready[i] |-> !push_valid[i])
    end
  end

  for (genvar j = 0; j < NumPopFlows; j++) begin : gen_pop
    `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready[j]))
  end

  // ----------Sanity Check----------
  // if RegisterPopOutputs = 0, pop_valid could be unstable if push_valid or push_dest_id is unstable
  if ((EnableAssertPushValidStability && EnableAssertPushDestinationStability) ||
      RegisterPopOutputs) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a,
               pop_valid[fv_pop_id] && !pop_ready[fv_pop_id] |=> pop_valid[fv_pop_id])
  end
  // pop_data can only be stable if it is registered at the output
  if (RegisterPopOutputs) begin : gen_pop_data
    `BR_ASSERT(pop_data_stable_a,
               pop_valid[fv_pop_id] && !pop_ready[fv_pop_id] |=> $stable(pop_data[fv_pop_id]))
  end

  // If RegisterDemuxOutputs = 1, registers are inserted between the demux and mux to break up the
  // timing path, increasing the cut-through latency by 1.
  if (RegisterDemuxOutputs | RegisterPopOutputs) begin : gen_lat
    `BR_ASSERT(pop_valid_forward_progress_a, |push_valid |-> ##Latency |pop_valid)
  end else begin : gen_lat0
    `BR_ASSERT(pop_valid_forward_progress_a, |push_valid |-> |pop_valid)
  end

  // ----------Data integrity Check----------
  // data from same src/dest pair should be in order.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumPushFlows + Latency)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_vr),
      .incoming_data(push_data[fv_push_id]),
      .outgoing_vld(fv_pop_vr),
      .outgoing_data(pop_data[fv_pop_id])
  );

endmodule : br_flow_xbar_basic_fpv_monitor
