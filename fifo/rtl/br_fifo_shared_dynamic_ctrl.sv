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
// Bedrock-RTL Shared Dynamic Multi-FIFO Controller (Push Valid/Ready Interface)
//
// This module implements the controller for a shared storage multi-FIFO
// with dynamic allocation.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs dynamically.
// The order of RAM entries for a single logical FIFO is tracked via
// singly-linked lists. The linked lists are stored in a separate
// pointer RAM. The data and pointer RAMs must be instantiated
// externally to this module and connected to the `data_ram_*` and
// `ptr_ram_*` ports.
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
// determined by the formula `StagingBufferDepth / (PointerRamReadLatency + 1)`.
// To get one pop per cycle bandwidth for a single logical FIFO, the staging
// buffer depth should be set to `PointerRamReadLatency + 1`.

`include "br_asserts_internal.svh"

module br_fifo_shared_dynamic_ctrl #(
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
    // The bandwidth will be `StagingBufferDepth / (PointerRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int DataRamReadLatency = 0,
    // The number of cycles between pointer ram read address and read data. Must be >=0.
    parameter int PointerRamReadLatency = 0,
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
    output logic [NumFifos-1:0][Width-1:0] pop_data,

    // Data RAM Ports
    output logic [NumWritePorts-1:0] data_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    output logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // Pointer RAM Ports
    output logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,

    output logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data
);

  // Integration Checks
  `BR_ASSERT_STATIC(num_write_ports_in_range_a, NumWritePorts >= 1)
  `BR_ASSERT_STATIC(legal_num_read_ports_a, NumReadPorts >= 1 && br_math::is_power_of_2(
                    NumReadPorts))
  `BR_ASSERT_STATIC(num_fifos_in_range_a, NumFifos >= 1)
  `BR_ASSERT_STATIC(depth_in_range_a, Depth > 2 * NumWritePorts)
  `BR_ASSERT_STATIC(width_in_range_a, Width >= 1)
  `BR_ASSERT_STATIC(staging_buffer_depth_in_range_a, StagingBufferDepth >= 1)
  `BR_ASSERT_STATIC(pointer_ram_read_latency_in_range_a, PointerRamReadLatency >= 0)
  `BR_ASSERT_STATIC(data_ram_read_latency_in_range_a, DataRamReadLatency >= 0)

  // Other integration checks in submodules

  // Implementation

  // Push Controller

  logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid;
  logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail;
  logic [NumFifos-1:0] dealloc_valid;
  logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id;

  br_fifo_shared_dynamic_push_ctrl #(
      .NumWritePorts(NumWritePorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_push_ctrl (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .next_tail_valid,
      .next_tail,
      .dealloc_valid,
      .dealloc_entry_id
  );

  // Pointer Manager

  localparam int CountWidth = $clog2(Depth + 1);

  logic [NumFifos-1:0] ram_empty;
  logic [NumFifos-1:0][CountWidth-1:0] ram_items;
  logic [NumFifos-1:0] head_valid;
  logic [NumFifos-1:0] head_ready;
  logic [NumFifos-1:0][AddrWidth-1:0] head;

  br_fifo_shared_dynamic_ptr_mgr #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .NumLinkedListsPerFifo(StagingBufferDepth),
      .Depth(Depth),
      .RamReadLatency(PointerRamReadLatency)
  ) br_fifo_shared_dynamic_ptr_mgr (
      .clk,
      .rst,
      .next_tail_valid,
      .next_tail,
      .head_valid,
      .head_ready,
      .head,
      .empty(ram_empty),
      .items(ram_items),
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  // Pop Controller

  br_fifo_shared_pop_ctrl #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RamReadLatency(DataRamReadLatency),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterDeallocation(RegisterDeallocation)
  ) br_fifo_shared_pop_ctrl (
      .clk,
      .rst,
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .ram_items,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .dealloc_valid,
      .dealloc_entry_id
  );

  // Implementation Checks

  // TODO(zhemao): Add the checks

endmodule : br_fifo_shared_dynamic_ctrl
