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

// Bedrock-RTL Shared Pseudo-Static Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pstatic_flops_fpv_monitor #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 2,
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
    // Number of tiles in the depth dimension for the flop RAM.
    parameter int RamDepthTiles = 1,
    // Number of tiles in the width dimension for the flop RAM.
    parameter int RamWidthTiles = 1,
    // Number of stages on the address path for the flop RAM.
    parameter int RamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the flop RAM.
    parameter int RamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the flop RAM.
    parameter int RamReadDataWidthStages = 0,
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

    // Size configuration
    // These can come from straps or CSRs, but they must be set before reset is
    // deasserted and then held stable until reset is asserted.
    // The base and bound addresses determine the range of RAM addresses given
    // to each logical FIFO. They are both inclusive, so logical FIFO i will
    // increment from config_base[i] up to config_bound[i] before wrapping back
    // around to config_base[i] again.
    // The minimum size for a given logical FIFO is 1, meaning that
    // config_bound[i] must be >= config_base[i] for all i.
    // The address ranges must be in ascending order.
    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,
    // Error is asserted if the base and bound addresses are misconfigured.
    // For instance, if any address is >= Depth, config_base[i] > config_bound[i],
    // or config_base[i] <= config_bound[i-1] for i > 0.
    input logic config_error,

    // Push side
    input logic                   push_valid,
    input logic                   push_ready,
    input logic [      Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [   NumFifos-1:0] push_full,

    // Pop side
    input logic [NumFifos-1:0]            pop_valid,
    input logic [NumFifos-1:0]            pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0]            pop_empty
);

  localparam int RamReadLatency = RamAddressDepthStages +
                                  RamReadDataDepthStages +
                                  RamReadDataWidthStages;

  // ----------FIFO basic checks----------
  br_fifo_shared_pstatic_basic_fpv_monitor #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) fv_checker (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .push_full,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .pop_empty
  );

endmodule : br_fifo_shared_pstatic_flops_fpv_monitor

bind br_fifo_shared_pstatic_flops br_fifo_shared_pstatic_flops_fpv_monitor #(
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RamDepthTiles(RamDepthTiles),
    .RamWidthTiles(RamWidthTiles),
    .RamAddressDepthStages(RamAddressDepthStages),
    .RamReadDataDepthStages(RamReadDataDepthStages),
    .RamReadDataWidthStages(RamReadDataWidthStages),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
