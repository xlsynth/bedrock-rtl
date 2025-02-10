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
//
// Bedrock-RTL Shared Dynamic Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface)
//
// This module implements a shared storage multi-FIFO with dynamic allocation
// of storage from a flop-based RAM.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs dynamically.
// The order of RAM entries for a single logical FIFO is tracked via
// singly-linked lists. The linked lists are stored in a separate
// pointer RAM.
//
// The push interface provides a valid/ready interface and a binary-encoded
// FIFO ID. The push data is appended to the logical FIFO with the specified ID.
//
// The FIFO controller supports multiple write ports. There will be one push
// ready/valid interface for each write port. If there is sufficient space, the
// multi-FIFO can accept an item from every push interface on the same cycle,
// even if they are to the same logical FIFO.
//
// Every logical FIFO has its own ready/valid pop interface. If the data RAM
// read latency is non-zero or the RegisterPopOutputs parameter is set to 1, the
// pop_data will be provided from a staging buffer per logical FIFO. The staging
// buffers are refilled from the data RAM and arbitrate with each other for
// access. The controller supports multiple read ports. In this case, each
// logical FIFO can read from any of the read ports. The mapping of reads to
// ports is based on the lower bits of the read address. Each logical FIFO can
// only pop at most one item per cycle. Therefore, there must be at least as
// many active logical FIFOs as read ports to fully utilize the read bandwidth.
//
// Because the pop bandwidth of a linked list is limited by the pointer RAM read
// latency, the multi-FIFO supports using multiple linked lists per logical
// FIFO. The linked list controller will cycle through the linked list heads in
// round-robin fashion. The number of linked lists per FIFO is determined by the
// staging buffer depth.  The bandwidth of a single logical FIFO is thus
// determined by the formula `StagingBufferDepth / (PointerRamReadLatency + 1)`,
// where `PointerRamReadLatency = PointerRamAddressDepthStages +
// PointerRamReadDataDepthStages + PointerRamReadDataWidthStages`. To get one
// pop per cycle bandwidth for a single logical FIFO, the staging buffer depth
// should be set to `PointerRamReadLatency + 1`.
//
// For example, to have zero retiming on the read path, full bandwidth, and
// pop data registered at the output, set StagingBufferDepth = 1 and
// RegisterPopOutputs = 1.

module br_fifo_shared_dynamic_flops #(
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
    output logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,

    // Pop side
    output logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data
);
  // Integration Checks
  // Rely on checks in the submodules

  // Implementation
  // Data RAM
  logic [NumWritePorts-1:0] data_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr;
  logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data;

  logic [NumReadPorts-1:0] data_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr;
  logic [NumReadPorts-1:0] data_ram_rd_data_valid;
  logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(DataRamDepthTiles),
      .WidthTiles(DataRamWidthTiles),
      .AddressDepthStages(DataRamAddressDepthStages),
      .ReadDataDepthStages(DataRamReadDataDepthStages),
      .ReadDataWidthStages(DataRamReadDataWidthStages)
  ) br_ram_flops_data (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(data_ram_wr_valid),
      .wr_addr(data_ram_wr_addr),
      .wr_data(data_ram_wr_data),
      .wr_word_en({NumWritePorts{1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(data_ram_rd_addr_valid),
      .rd_addr(data_ram_rd_addr),
      .rd_data_valid(data_ram_rd_data_valid),
      .rd_data(data_ram_rd_data)
  );

  // Pointer RAM
  logic [NumWritePorts-1:0] ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data;

  logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr;
  logic [NumReadPorts-1:0] ptr_ram_rd_data_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(AddrWidth),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(PointerRamDepthTiles),
      .WidthTiles(PointerRamWidthTiles),
      .AddressDepthStages(PointerRamAddressDepthStages),
      .ReadDataDepthStages(PointerRamReadDataDepthStages),
      .ReadDataWidthStages(PointerRamReadDataWidthStages)
  ) br_ram_flops_pointer (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(ptr_ram_wr_valid),
      .wr_addr(ptr_ram_wr_addr),
      .wr_data(ptr_ram_wr_data),
      .wr_word_en({NumWritePorts{1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(ptr_ram_rd_addr_valid),
      .rd_addr(ptr_ram_rd_addr),
      .rd_data_valid(ptr_ram_rd_data_valid),
      .rd_data(ptr_ram_rd_data)
  );

  // Controller
  localparam int DataRamReadLatency =
      DataRamAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages;
  localparam int PointerRamReadLatency =
      PointerRamAddressDepthStages + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages;

  br_fifo_shared_dynamic_ctrl #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation),
      .DataRamReadLatency(DataRamReadLatency),
      .PointerRamReadLatency(PointerRamReadLatency),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_ctrl (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  // Implementation Checks

  // Rely on implementation checks in the controller

endmodule
