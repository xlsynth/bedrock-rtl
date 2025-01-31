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

// Bedrock-RTL CDC FIFO (Internal 1R1W Flop-RAM, Push Ready/Valid, Pop Ready/Valid Variant)
//
// A one-read/one-write (1R1W) asynchronous FIFO that uses the AMBA-inspired
// ready-valid handshake protocol for synchronizing pipeline stages and stalling
// when encountering backpressure hazards.
//
// This module includes an internal flop-RAM.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// The RegisterPopOutputs parameter can be set to 1 to add an additional br_flow_reg_fwd
// before the pop interface of the FIFO. This may improve timing of paths dependent on
// the pop interface at the expense of an additional pop cycle of cut-through latency.

// The cut-through latency (push_valid to pop_valid latency) and backpressure
// latency (pop_ready to push_ready) can be calculated as follows:
//
// Let PushT and PopT be the push period and pop period, respectively.
//
// The cut-through latency is max(2, FlopRamAddressDepthStages + 2) * PushT +
// (NumSyncStages + 1 + FlopRamAddressDepthStages + FlopRamReadDataDepthStages +
// FlopRamReadDataWidthStages + RegisterPopOutputs) * PopT.

// The backpressure latency is 2 * PopT + (NumSyncStages + 1) * PushT.
//
// To achieve full bandwidth, the depth of the FIFO must be at least
// (CutThroughLatency + BackpressureLatency) / max(PushT, PopT).

module br_cdc_fifo_flops #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data comes directly from push_valid (if bypass is enabled)
    // and/or ram_wr_data.
    parameter bit RegisterPopOutputs = 0,
    // Number of synchronization stages to use for the gray counts. Must be >=2.
    parameter int NumSyncStages = 3,
    // Number of tiles in the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int FlopRamDepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int FlopRamWidthTiles = 1,
    // Number of pipeline register stages inserted along the write address and read address paths
    // in the depth dimension. Must be at least 0.
    parameter int FlopRamAddressDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the depth dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the width dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataWidthStages = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,

    // Internal computed parameters
    localparam int AddrWidth  = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Posedge-triggered clock.
    input logic pop_clk,
    // Synchronous active-high reset.
    input logic pop_rst,

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Push-side status flags
    output logic push_full,
    output logic push_full_next,
    output logic [CountWidth-1:0] push_slots,
    output logic [CountWidth-1:0] push_slots_next,

    // Pop-side status flags
    output logic pop_empty,
    output logic pop_empty_next,
    output logic [CountWidth-1:0] pop_items,
    output logic [CountWidth-1:0] pop_items_next
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic push_ram_wr_valid;
  logic [AddrWidth-1:0] push_ram_wr_addr;
  logic [Width-1:0] push_ram_wr_data;
  logic pop_ram_rd_addr_valid;
  logic [AddrWidth-1:0] pop_ram_rd_addr;
  logic pop_ram_rd_data_valid;
  logic [Width-1:0] pop_ram_rd_data;

  br_cdc_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_ctrl_1r1w (
      .push_clk,
      .push_rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .push_full,
      .push_full_next,
      .push_slots,
      .push_slots_next,
      .pop_empty,
      .pop_empty_next,
      .pop_items,
      .pop_items_next,
      .push_ram_wr_valid,
      .push_ram_wr_addr,
      .push_ram_wr_data,
      .pop_ram_rd_addr_valid,
      .pop_ram_rd_addr,
      .pop_ram_rd_data_valid,
      .pop_ram_rd_data
  );

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .DepthTiles(FlopRamDepthTiles),
      .WidthTiles(FlopRamWidthTiles),
      .AddressDepthStages(FlopRamAddressDepthStages),
      .ReadDataDepthStages(FlopRamReadDataDepthStages),
      .ReadDataWidthStages(FlopRamReadDataWidthStages),
      // Flops don't need to be reset, since uninitialized cells will never be read
      .EnableMemReset(0),
      // Since there is an asynchronous path on the read,
      // we need to use structured gates for the read mux.
      .UseStructuredGates(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_ram_flops (
      .wr_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(push_rst),
      .wr_valid(push_ram_wr_valid),
      .wr_addr(push_ram_wr_addr),
      .wr_data(push_ram_wr_data),
      .wr_word_en(1'b1),  // no partial write
      .rd_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(pop_rst),
      .rd_addr_valid(pop_ram_rd_addr_valid),
      .rd_addr(pop_ram_rd_addr),
      .rd_data_valid(pop_ram_rd_data_valid),
      .rd_data(pop_ram_rd_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_cdc_fifo_flops
