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

// Bedrock-RTL Shared Dynamic Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface) FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_flops_fpv_monitor #(
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
    // Number of tiles in the depth dimension for the data flop RAM.
    parameter int DataRamDepthTiles = 1,
    // Number of tiles in the width dimension for the data flop RAM.
    parameter int DataRamWidthTiles = 1,
    // Number of stages on the address path for the data flop RAM.
    parameter int DataRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the data flop RAM.
    parameter int DataRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the data flop RAM.
    parameter int DataRamReadDataWidthStages = 0,
    // Number of tiles in the depth dimension for the pointer flop RAM.
    parameter int PointerRamDepthTiles = 1,
    // Number of tiles in the width dimension for the pointer flop RAM.
    parameter int PointerRamWidthTiles = 1,
    // Number of stages on the address path for the pointer flop RAM.
    parameter int PointerRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the pointer flop RAM.
    parameter int PointerRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the pointer flop RAM.
    parameter int PointerRamReadDataWidthStages = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth)
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

  // ----------FIFO basic checks----------
  br_fifo_shared_dynamic_basic_fpv_monitor #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) fv_checker (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .pop_valid,
      .pop_ready,
      .pop_data
  );

endmodule : br_fifo_shared_dynamic_flops_fpv_monitor

bind br_fifo_shared_dynamic_flops br_fifo_shared_dynamic_flops_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RegisterDeallocation(RegisterDeallocation),
    .DataRamDepthTiles(DataRamDepthTiles),
    .DataRamWidthTiles(DataRamWidthTiles),
    .DataRamAddressDepthStages(DataRamAddressDepthStages),
    .DataRamReadDataDepthStages(DataRamReadDataDepthStages),
    .DataRamReadDataWidthStages(DataRamReadDataWidthStages),
    .PointerRamDepthTiles(PointerRamDepthTiles),
    .PointerRamWidthTiles(PointerRamWidthTiles),
    .PointerRamAddressDepthStages(PointerRamAddressDepthStages),
    .PointerRamReadDataDepthStages(PointerRamReadDataDepthStages),
    .PointerRamReadDataWidthStages(PointerRamReadDataWidthStages),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
