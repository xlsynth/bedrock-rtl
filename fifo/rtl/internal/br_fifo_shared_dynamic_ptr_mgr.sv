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
// Bedrock-RTL Shared Dynamic Multi-FIFO Pointer Manager

`include "br_asserts_internal.svh"

module br_fifo_shared_dynamic_ptr_mgr #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int NumLinkedListsPerFifo = 1,
    parameter int Depth = 2,
    parameter int RamReadLatency = 0,

    localparam int AddrWidth  = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid,
    input logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail,

    output logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,

    output logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data,

    input logic [NumFifos-1:0] head_ready,
    output logic [NumFifos-1:0] head_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] head,

    output logic [NumFifos-1:0] empty,
    output logic [NumFifos-1:0][CountWidth-1:0] items
);
  localparam int ReadPortIdWidth = $clog2(NumReadPorts);

  // Internal Integration Checks

  if (NumReadPorts > 1) begin : gen_multi_rport_checks
    for (genvar i = 0; i < NumFifos - 1; i++) begin : gen_inter_fifo_checks
      for (genvar j = i + 1; j < NumFifos; j++) begin : gen_inter_fifo_checks_inner
        // To ensure no conflicts on read ports, the pop control must make sure
        // not to simultaneously pop head pointers that are destined for the same
        // read port.
        `BR_ASSERT_IMPL(no_head_conflict_a,
                        ((head_ready[i] && head_valid[i]) &&
            (head_ready[j] && head_valid[j]))
            |->
          (head[i][ReadPortIdWidth-1:0] != head[j][ReadPortIdWidth-1:0]))
      end
    end
  end else begin : gen_single_rport_checks
    // With only one read port, we can only pop one head at a time.
    `BR_ASSERT_IMPL(onehot_head_pop_a, (|head_valid) |-> $onehot0(head_valid & head_ready))
  end

  // Implementation

  logic [NumFifos-1:0][NumWritePorts-1:0] fifo_ptr_ram_wr_valid;
  logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] fifo_ptr_ram_wr_addr;
  logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] fifo_ptr_ram_wr_data;

  logic [NumFifos-1:0][NumReadPorts-1:0] fifo_ptr_ram_rd_addr_valid;
  logic [NumFifos-1:0][NumReadPorts-1:0][AddrWidth-1:0] fifo_ptr_ram_rd_addr;
  logic [NumFifos-1:0][NumReadPorts-1:0] fifo_ptr_ram_rd_data_valid;
  logic [NumFifos-1:0][NumReadPorts-1:0][AddrWidth-1:0] fifo_ptr_ram_rd_data;

  for (genvar i = 0; i < NumFifos; i++) begin : gen_ll_ctrl
    // Instantiate a linked list controller for each FIFO.
    logic ctrl_ptr_ram_rd_addr_valid;
    logic [AddrWidth-1:0] ctrl_ptr_ram_rd_addr;
    logic ctrl_ptr_ram_rd_data_valid;
    logic [AddrWidth-1:0] ctrl_ptr_ram_rd_data;

    br_tracker_linked_list_ctrl #(
        .NumLinkedLists(NumLinkedListsPerFifo),
        .NumWritePorts(NumWritePorts),
        .Depth(Depth),
        .RamReadLatency(RamReadLatency)
    ) br_tracker_linked_list_ctrl (
        .clk(clk),
        .rst(rst),

        .next_tail_valid(next_tail_valid[i]),
        .next_tail(next_tail[i]),

        .ptr_ram_wr_valid(fifo_ptr_ram_wr_valid[i]),
        .ptr_ram_wr_addr (fifo_ptr_ram_wr_addr[i]),
        .ptr_ram_wr_data (fifo_ptr_ram_wr_data[i]),

        .ptr_ram_rd_addr_valid(ctrl_ptr_ram_rd_addr_valid),
        .ptr_ram_rd_addr(ctrl_ptr_ram_rd_addr),
        .ptr_ram_rd_data_valid(ctrl_ptr_ram_rd_data_valid),
        .ptr_ram_rd_data(ctrl_ptr_ram_rd_data),

        .head_valid(head_valid[i]),
        .head_ready(head_ready[i]),
        .head(head[i]),

        .empty(empty[i]),
        .items(items[i])
    );

    if (NumReadPorts > 1) begin : gen_multi_read
      // The lower bits of the address determine the read port.
      br_demux_bin #(
          .NumSymbolsOut(NumReadPorts),
          .SymbolWidth  (AddrWidth)
      ) br_demux_bin_fifo_ptr_ram_rd_addr (
          .select(ctrl_ptr_ram_rd_addr[ReadPortIdWidth-1:0]),
          .in_valid(ctrl_ptr_ram_rd_addr_valid),
          .in(ctrl_ptr_ram_rd_addr),
          .out_valid(fifo_ptr_ram_rd_addr_valid[i]),
          .out(fifo_ptr_ram_rd_addr[i])
      );

      // Only one of the read data should be valid on a given cycle.
      assign ctrl_ptr_ram_rd_data_valid = |fifo_ptr_ram_rd_data_valid[i];
      br_mux_onehot #(
          .NumSymbolsIn(NumReadPorts),
          .SymbolWidth (AddrWidth)
      ) br_mux_onehot_fifo_ptr_ram_rd_data (
          .select(fifo_ptr_ram_rd_data_valid[i]),
          .in(fifo_ptr_ram_rd_data[i]),
          .out(ctrl_ptr_ram_rd_data)
      );
    end else begin : gen_single_read
      assign fifo_ptr_ram_rd_addr_valid[i] = ctrl_ptr_ram_rd_addr_valid;
      assign fifo_ptr_ram_rd_addr[i] = ctrl_ptr_ram_rd_addr;
      assign ctrl_ptr_ram_rd_data_valid = fifo_ptr_ram_rd_data_valid[i];
      assign ctrl_ptr_ram_rd_data = fifo_ptr_ram_rd_data[i];
    end
  end

  // Mux the FIFOs for each write port.
  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_write_mux
    logic [NumFifos-1:0] wport_fifo_ptr_ram_wr_valid;
    logic [NumFifos-1:0][AddrWidth-1:0] wport_fifo_ptr_ram_wr_addr;
    logic [NumFifos-1:0][AddrWidth-1:0] wport_fifo_ptr_ram_wr_data;

    for (genvar j = 0; j < NumFifos; j++) begin : gen_fifo_mux
      assign wport_fifo_ptr_ram_wr_valid[j] = fifo_ptr_ram_wr_valid[j][i];
      assign wport_fifo_ptr_ram_wr_addr[j]  = fifo_ptr_ram_wr_addr[j][i];
      assign wport_fifo_ptr_ram_wr_data[j]  = fifo_ptr_ram_wr_data[j][i];
    end

    assign ptr_ram_wr_valid[i] = |wport_fifo_ptr_ram_wr_valid;

    br_mux_onehot #(
        .NumSymbolsIn(NumFifos),
        .SymbolWidth (AddrWidth)
    ) br_mux_onehot_fifo_ptr_ram_wr_addr (
        .select(wport_fifo_ptr_ram_wr_valid),
        .in(wport_fifo_ptr_ram_wr_addr),
        .out(ptr_ram_wr_addr[i])
    );

    br_mux_onehot #(
        .NumSymbolsIn(NumFifos),
        .SymbolWidth (AddrWidth)
    ) br_mux_onehot_fifo_ptr_ram_wr_data (
        .select(wport_fifo_ptr_ram_wr_valid),
        .in(wport_fifo_ptr_ram_wr_data),
        .out(ptr_ram_wr_data[i])
    );
  end

  // Mux the FIFOs for each read port.
  for (genvar i = 0; i < NumReadPorts; i++) begin : gen_read_mux
    logic [NumFifos-1:0] rport_fifo_ptr_ram_rd_addr_valid;
    logic [NumFifos-1:0][AddrWidth-1:0] rport_fifo_ptr_ram_rd_addr;
    logic [NumFifos-1:0] rport_fifo_ptr_ram_rd_data_valid;
    logic [NumFifos-1:0][AddrWidth-1:0] rport_fifo_ptr_ram_rd_data;

    for (genvar j = 0; j < NumFifos; j++) begin : gen_fifo_mux
      assign rport_fifo_ptr_ram_rd_addr_valid[j] = fifo_ptr_ram_rd_addr_valid[j][i];
      assign rport_fifo_ptr_ram_rd_addr[j] = fifo_ptr_ram_rd_addr[j][i];
      assign fifo_ptr_ram_rd_data_valid[j][i] = rport_fifo_ptr_ram_rd_data_valid[j];
      assign fifo_ptr_ram_rd_data[j][i] = rport_fifo_ptr_ram_rd_data[j];
    end

    logic [NumFifos-1:0] rport_ptr_ram_rd_data_fifo_onehot;

    assign ptr_ram_rd_addr_valid[i] = |rport_fifo_ptr_ram_rd_addr_valid;

    br_mux_onehot #(
        .NumSymbolsIn(NumFifos),
        .SymbolWidth (AddrWidth)
    ) br_mux_onehot_fifo_ptr_ram_rd_addr (
        .select(rport_fifo_ptr_ram_rd_addr_valid),
        .in(rport_fifo_ptr_ram_rd_addr),
        .out(ptr_ram_rd_addr[i])
    );

    br_delay_valid #(
        .NumStages(RamReadLatency),
        .Width(NumFifos)
    ) br_delay_valid_fifo_ptr_ram_rd_data_valid (
        .clk(clk),
        .rst(rst),
        .in_valid(ptr_ram_rd_addr_valid[i]),
        .in(rport_fifo_ptr_ram_rd_addr_valid),
        .out_valid(),
        .out(rport_ptr_ram_rd_data_fifo_onehot),
        .out_valid_stages(),
        .out_stages()
    );

    assign rport_fifo_ptr_ram_rd_data_valid =
        {NumFifos{ptr_ram_rd_data_valid[i]}} & rport_ptr_ram_rd_data_fifo_onehot;
    assign rport_fifo_ptr_ram_rd_data = {NumFifos{ptr_ram_rd_data[i]}};
  end
endmodule
