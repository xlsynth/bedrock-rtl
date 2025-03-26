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

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pop_ctrl #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    parameter bit RegisterDeallocation = 0,

    localparam int AddrWidth  = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
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

    output logic [NumFifos-1:0] dealloc_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);

  // Internal Integration Checks

  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFifos),
      .Width(AddrWidth)
  ) br_flow_checks_valid_data_impl_head (
      .clk,
      .rst,
      .valid(head_valid),
      .ready(head_ready),
      .data (head)
  );

  // Implementation
  localparam bit NoStagingBuffer = (RamReadLatency == 0) && !RegisterPopOutputs;

  logic [NumFifos-1:0] fifo_ram_rd_addr_valid;
  logic [NumFifos-1:0] fifo_ram_rd_addr_ready;
  logic [NumFifos-1:0][AddrWidth-1:0] fifo_ram_rd_addr;
  logic [NumFifos-1:0] fifo_ram_rd_data_valid;
  logic [NumFifos-1:0][Width-1:0] fifo_ram_rd_data;

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_ram_read
    logic ram_rd_req_valid;
    logic ram_rd_req_ready;

    if (NoStagingBuffer) begin : gen_no_buffer
      assign ram_rd_req_valid = !ram_empty[i] && pop_ready[i];
      assign pop_valid[i] = fifo_ram_rd_data_valid[i];
      assign pop_data[i] = fifo_ram_rd_data[i];

      `BR_UNUSED(ram_rd_req_ready)  // used for assertion only
      `BR_ASSERT_IMPL(zero_read_latency_a,
                      (ram_rd_req_valid && ram_rd_req_ready) |-> fifo_ram_rd_data_valid[i])
    end else begin : gen_staging_buffer
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
          .pop_data (pop_data[i])
      );
    end

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

    assign fifo_ram_rd_addr[i] = head[i];
  end

  if (NoStagingBuffer) begin : gen_no_buffer_unused
    `BR_UNUSED(ram_items)
  end else begin : gen_buffer_unused
    `BR_UNUSED(ram_empty)
  end

  // Read Crossbar
  // TODO(zhemao): Support an option to have dedicated read ports for a FIFO
  // or group of FIFOs instead of spreading reads across all read ports.
  br_fifo_shared_read_xbar #(
      .NumFifos(NumFifos),
      .NumReadPorts(NumReadPorts),
      .AddrWidth(AddrWidth),
      .Width(Width),
      .RamReadLatency(RamReadLatency)
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
      .pop_rd_data(data_ram_rd_data)
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
