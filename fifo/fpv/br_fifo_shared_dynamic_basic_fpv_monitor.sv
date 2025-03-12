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

// br_fifo_shared_dynamic basic FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_basic_fpv_monitor #(
    // Number of write ports. Must be >=1.
    parameter int NumWritePorts = 1,
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=1.
    parameter int NumFifos = 1,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 3,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (PointerRamAddressDepthStages
    // + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    // Pop side
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data
);

  // ----------FV Modeling Code----------
  localparam int PortWidth = br_math::clamped_clog2(NumWritePorts);
  // pick a random FIFO to check
  logic [FifoIdWidth-1:0] fv_fifo_id;
  // pick a random write port for assertion
  logic [PortWidth-1:0] fv_wr_port;
  logic [NumWritePorts-1:0] fv_push_vr;

  `BR_ASSUME(fv_fifo_id_a, $stable(fv_fifo_id) && (fv_fifo_id < NumFifos))
  `BR_ASSUME(fv_wr_prt_a, $stable(fv_wr_port) && (fv_wr_port < NumWritePorts))

  // tracking valid push to fv_fifo_id
  always_comb begin
    fv_push_vr = 'd0;
    for (int n = 0; n < NumWritePorts; n++) begin
      fv_push_vr[n] = push_valid[n] && push_ready[n] && (push_fifo_id[n] == fv_fifo_id);
    end
  end

  // ----------FV assumptions----------
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_asm
    if (EnableAssertPushValidStability) begin : gen_push_valid_stable
      `BR_ASSUME(push_valid_stable_a, push_valid[i] && !push_ready[i] |=> push_valid[i])
    end
    if (EnableAssertPushDataStability) begin : gen_push_data_stable
      `BR_ASSUME(
          push_data_stable_a,
          push_valid[i] && !push_ready[i] |=> $stable(push_data[i]) && $stable(push_fifo_id[i]))
    end
  end

  // ----------FV assertions----------
  // RTL guarantees pop_valid && !pop_ready is not possible, so there is no check
  for (genvar i = 0; i < NumFifos; i++) begin : gen_ast
    `BR_ASSUME(pop_ready_liveness_a, s_eventually pop_ready[i])
  end
  `BR_ASSERT(no_deadlock_pop_a, fv_push_vr[fv_wr_port] |-> s_eventually pop_valid[fv_fifo_id])

  // ----------Data integrity Check----------
  // data pushed to same FIFO should be in order
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(NumWritePorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(Depth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_vr),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid[fv_fifo_id] & pop_ready[fv_fifo_id]),
      .outgoing_data(pop_data[fv_fifo_id])
  );

endmodule : br_fifo_shared_dynamic_basic_fpv_monitor
