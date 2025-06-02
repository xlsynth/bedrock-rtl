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
// Bedrock-RTL Shared Multi-FIFO Pop Controller
//
// This module implements the pop-side control logic for a shared multi-FIFO.
//
// It manages multiple logical FIFOs that share a common storage RAM. Each logical FIFO
// has its own pop interface (valid/ready/data). The module coordinates reading data
// from the shared RAM, refilling per-FIFO staging buffers, and deallocating entries.
//
// The pop bandwidth per FIFO is determined by the staging buffer depth and the RAM read
// latency. The module supports pipelined RAM reads and optional output registering.
//
// The module arbitrates RAM read requests among the logical FIFOs, tracks the head
// pointers of each FIFO, and generates deallocation signals when entries are popped.
//
// The design assumes that the RAM and pointer management are handled externally.
//
// This is identical to br_fifo_shared_pop_ctrl, but with an external arbiter interface so
// that an arbitrary arbitration policy can be chosen for the pop side of the FIFO (where
// NumReadPorts < NumFifos).

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pop_ctrl_ext_arbiter #(
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=1.
    parameter int NumFifos = 1,
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
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int RamReadLatency = 0,

    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int ArbDataWidth = AddrWidth + $clog2(NumFifos)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    output logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,
    input logic [NumFifos-1:0][CountWidth-1:0] ram_items,

    output logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0] pop_empty,

    output logic [NumFifos-1:0] dealloc_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // External arbiter interface
    output logic [NumReadPorts-1:0][NumFifos-1:0] arb_push_valid,
    output logic [NumReadPorts-1:0][NumFifos-1:0][ArbDataWidth-1:0] arb_push_data,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_push_ready,
    input logic [NumReadPorts-1:0] arb_pop_valid,
    input logic [NumReadPorts-1:0][ArbDataWidth-1:0] arb_pop_data,
    output logic [NumReadPorts-1:0] arb_pop_ready
);

  // Integration Checks

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFifos),
      .Width(AddrWidth)
  ) br_flow_checks_valid_data_intg_head (
      .clk,
      .rst,
      .valid(head_valid),
      .ready(head_ready),
      .data (head)
  );

  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_intg_checks
    `BR_ASSERT_INTG(no_head_valid_on_empty_a, ram_empty[i] |-> !head_valid[i])
  end

  // Implementation
  localparam bit HasStagingBuffer = (RamReadLatency > 0) || RegisterPopOutputs;

  logic [NumFifos-1:0] fifo_ram_rd_addr_valid;
  logic [NumFifos-1:0] fifo_ram_rd_addr_ready;
  logic [NumFifos-1:0][AddrWidth-1:0] fifo_ram_rd_addr;
  logic [NumFifos-1:0] fifo_ram_rd_data_valid;
  logic [NumFifos-1:0][Width-1:0] fifo_ram_rd_data;

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_ram_read
    if (!HasStagingBuffer) begin : gen_no_buffer
      br_flow_fork #(
          .NumFlows(2)
      ) br_flow_fork_head (
          .clk,
          .rst,
          .push_valid(head_valid[i]),
          .push_ready(head_ready[i]),
          .pop_valid_unstable({fifo_ram_rd_addr_valid[i], pop_valid[i]}),
          .pop_ready({fifo_ram_rd_addr_ready[i], pop_ready[i]})
      );

      assign pop_data[i]  = fifo_ram_rd_data[i];
      assign pop_empty[i] = ram_empty[i];

      `BR_ASSERT_IMPL(zero_read_latency_a,
                      (pop_valid[i] && pop_ready[i]) |-> fifo_ram_rd_data_valid[i])
    end else begin : gen_staging_buffer
      logic ram_rd_req_valid;
      logic ram_rd_req_ready;
      logic stg_buffer_empty;

      br_fifo_staging_buffer #(
          .EnableBypass(0),
          .TotalDepth(Depth),
          .BufferDepth(StagingBufferDepth),
          .Width(Width),
          .RegisterPopOutputs(RegisterPopOutputs),
          .RamReadLatency(RamReadLatency),
          .TotalItemsIncludesStaged(0)
      ) br_fifo_staging_buffer (
          .clk,
          .rst,

          .total_items(ram_items[i]),

          .bypass_valid_unstable(1'b0),
          .bypass_data_unstable(Width'(1'b0)),
          .bypass_ready(),

          .ram_rd_addr_ready(ram_rd_req_ready),
          .ram_rd_addr_valid(ram_rd_req_valid),
          .ram_rd_data_valid(fifo_ram_rd_data_valid[i]),
          .ram_rd_data(fifo_ram_rd_data[i]),

          .pop_ready(pop_ready[i]),
          .pop_valid(pop_valid[i]),
          .pop_data (pop_data[i]),
          .pop_empty(stg_buffer_empty)
      );

      br_flow_join #(
          .NumFlows(2)
      ) br_flow_join_ram_rd_addr (
          .clk,
          .rst,

          .push_valid({head_valid[i], ram_rd_req_valid}),
          .push_ready({head_ready[i], ram_rd_req_ready}),
          .pop_valid (fifo_ram_rd_addr_valid[i]),
          .pop_ready (fifo_ram_rd_addr_ready[i])
      );

      assign pop_empty[i] = ram_empty[i] && stg_buffer_empty;
    end

    assign fifo_ram_rd_addr[i] = head[i];
  end

  if (!HasStagingBuffer) begin : gen_no_buffer_unused
    `BR_UNUSED_NAMED(no_staging_buffer_unused, {ram_items, fifo_ram_rd_data_valid})
  end

  // Read Crossbar
  // TODO(zhemao): Support an option to have dedicated read ports for a FIFO
  // or group of FIFOs instead of spreading reads across all read ports.
  br_fifo_shared_read_xbar #(
      .NumFifos(NumFifos),
      .NumReadPorts(NumReadPorts),
      .AddrWidth(AddrWidth),
      .Width(Width),
      .RamReadLatency(RamReadLatency),
      // If there is no staging buffer, the read request can be revoked if
      // pop_ready becomes low.
      .EnableAssertPushValidStability(HasStagingBuffer)
  ) br_fifo_shared_read_xbar (
      .clk,
      .rst,

      .push_rd_addr_valid(fifo_ram_rd_addr_valid),
      .push_rd_addr_ready(fifo_ram_rd_addr_ready),
      .push_rd_addr(fifo_ram_rd_addr),
      .push_rd_data_valid(fifo_ram_rd_data_valid),
      .push_rd_data(fifo_ram_rd_data),

      .pop_rd_addr_valid(data_ram_rd_addr_valid),
      .pop_rd_addr(data_ram_rd_addr),
      .pop_rd_data_valid(data_ram_rd_data_valid),
      .pop_rd_data(data_ram_rd_data),

      .arb_push_valid,
      .arb_push_data,
      .arb_push_ready,
      .arb_pop_valid,
      .arb_pop_data,
      .arb_pop_ready
  );

  if (RegisterDeallocation) begin : gen_reg_dealloc
    logic [NumFifos-1:0] dealloc_valid_next;

    assign dealloc_valid_next = head_valid & head_ready;
    `BR_REG(dealloc_valid, dealloc_valid_next)

    for (genvar i = 0; i < NumFifos; i++) begin : gen_reg_dealloc_entry_id
      `BR_REGL(dealloc_entry_id[i], head[i], dealloc_valid_next[i])
    end
  end else begin : gen_no_reg_dealloc
    assign dealloc_valid = head_valid & head_ready;
    assign dealloc_entry_id = head;
  end

endmodule
