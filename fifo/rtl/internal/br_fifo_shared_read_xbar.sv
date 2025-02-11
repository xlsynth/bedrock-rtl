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
// Bedrock-RTL Shared Multi-FIFO RAM Read Crossbar

`include "br_asserts_internal.svh"
`include "br_unused.svh"
module br_fifo_shared_read_xbar #(
    parameter int NumFifos = 2,
    parameter int NumReadPorts = 1,
    parameter int RamReadLatency = 0,
    parameter int AddrWidth = 1,
    parameter int Width = 1
) (
    // ri lint_check_waive HIER_NET_NOT_READ INPUT_NOT_READ
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] push_rd_addr_valid,
    output logic [NumFifos-1:0] push_rd_addr_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] push_rd_addr,
    output logic [NumFifos-1:0] push_rd_data_valid,
    output logic [NumFifos-1:0][Width-1:0] push_rd_data,

    output logic [NumReadPorts-1:0] pop_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] pop_rd_addr,
    input logic [NumReadPorts-1:0] pop_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] pop_rd_data
);

  `BR_ASSERT_STATIC(legal_num_fifos_a, NumFifos >= 2)
  // For now, restrict read ports to powers of two so that we don't have to do modulo operations.
  // TODO(zhemao): Remove this restriction once we have efficient modulo block.
  `BR_ASSERT_STATIC(legal_num_read_ports_a, NumReadPorts >= 1 && br_math::is_power_of_2(
                    NumReadPorts))
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= $clog2(NumReadPorts))

  // Read Address Demux per FIFO

  logic [NumFifos-1:0][NumReadPorts-1:0] demuxed_rd_addr_valid;
  logic [NumFifos-1:0][NumReadPorts-1:0] demuxed_rd_addr_ready;
  logic [NumFifos-1:0][NumReadPorts-1:0][AddrWidth-1:0] demuxed_rd_addr;

  if (NumReadPorts == 1) begin : gen_no_demux_rd_addr
    assign demuxed_rd_addr_valid = push_rd_addr_valid;
    assign push_rd_addr_ready = demuxed_rd_addr_ready;
    assign demuxed_rd_addr = push_rd_addr;
  end else begin : gen_demux_rd_addr
    localparam int PortIdWidth = $clog2(NumReadPorts);

    for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_demux
      logic [PortIdWidth-1:0] fifo_port_id;

      assign fifo_port_id = push_rd_addr[i][PortIdWidth-1:0];

      br_flow_demux_select_unstable #(
          .NumFlows(NumReadPorts),
          .Width(AddrWidth)
      ) br_flow_demux_select_unstable_inst (
          .clk,
          .rst,
          .select(fifo_port_id),
          .push_valid(push_rd_addr_valid[i]),
          .push_ready(push_rd_addr_ready[i]),
          .push_data(push_rd_addr[i]),
          .pop_valid_unstable(demuxed_rd_addr_valid[i]),
          .pop_ready(demuxed_rd_addr_ready[i]),
          .pop_data_unstable(demuxed_rd_addr[i])
      );
    end
  end

  // Read Address Mux and Data Demux per Read Port

  logic [NumReadPorts-1:0][NumFifos-1:0] demuxed_rd_data_valid;
  logic [NumReadPorts-1:0][NumFifos-1:0][Width-1:0] demuxed_rd_data;

  localparam int FifoIdWidth = $clog2(NumFifos);
  localparam int TotalMuxWidth = FifoIdWidth + AddrWidth;

  logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_rd_addr_fifo_id;
  logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_rd_data_fifo_id;
  logic [NumReadPorts-1:0] pop_rd_data_fifo_id_valid;

  for (genvar i = 0; i < NumReadPorts; i++) begin : gen_read_port_mux
    logic [NumFifos-1:0] mux_push_ready;
    logic [NumFifos-1:0] mux_push_valid;
    logic [NumFifos-1:0][TotalMuxWidth-1:0] mux_push_data;

    for (genvar j = 0; j < NumFifos; j++) begin : gen_mux_input
      assign mux_push_valid[j] = demuxed_rd_addr_valid[j][i];
      assign mux_push_data[j] = {demuxed_rd_addr[j][i], FifoIdWidth'($unsigned(j))};
      assign demuxed_rd_addr_ready[j][i] = mux_push_ready[j];
    end

    // TODO(zhemao): Allow selection of different arbitration policy.
    br_flow_mux_lru #(
        .NumFlows(NumFifos),
        .Width(TotalMuxWidth)
    ) br_flow_mux_lru_inst (
        .clk,
        .rst,
        .push_valid(mux_push_valid),
        .push_ready(mux_push_ready),
        .push_data (mux_push_data),
        .pop_valid (pop_rd_addr_valid[i]),
        .pop_ready (1'b1),
        .pop_data  ({pop_rd_addr[i], pop_rd_addr_fifo_id[i]})
    );

    br_delay_valid #(
        .NumStages(RamReadLatency),
        .Width(FifoIdWidth)
    ) br_delay_valid_fifo_id (
        .clk,
        .rst,
        .in_valid(pop_rd_addr_valid[i]),
        .in(pop_rd_addr_fifo_id[i]),
        .out_valid(pop_rd_data_fifo_id_valid[i]),
        .out(pop_rd_data_fifo_id[i]),
        .out_valid_stages(),
        .out_stages()
    );

    br_demux_bin #(
        .NumSymbolsOut(NumFifos),
        .SymbolWidth  (Width)
    ) br_demux_bin_rd_data (
        .select(pop_rd_data_fifo_id[i]),
        .in_valid(pop_rd_data_valid[i]),
        .in(pop_rd_data[i]),
        .out_valid(demuxed_rd_data_valid[i]),
        .out(demuxed_rd_data[i])
    );
  end

  `BR_UNUSED(pop_rd_data_fifo_id_valid)  // Used for assertion only
  `BR_ASSERT_IMPL(expected_read_latency_a, pop_rd_data_fifo_id_valid == pop_rd_data_valid)

  // Read Data Mux per Read Port

  if (NumReadPorts == 1) begin : gen_no_mux_rd_data
    assign push_rd_data_valid = demuxed_rd_data_valid;
    assign push_rd_data = demuxed_rd_data;
  end else begin : gen_mux_rd_data
    for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_rd_data
      logic [NumReadPorts-1:0] mux_in_rd_data_valid;
      logic [NumReadPorts-1:0][Width-1:0] mux_in_rd_data;

      for (genvar j = 0; j < NumReadPorts; j++) begin : gen_mux_input
        assign mux_in_rd_data_valid[j] = demuxed_rd_data_valid[j][i];
        assign mux_in_rd_data[j] = demuxed_rd_data[j][i];
      end

      assign push_rd_data_valid[i] = |mux_in_rd_data_valid;
      br_mux_onehot #(
          .NumSymbolsIn(NumReadPorts),
          .SymbolWidth (Width)
      ) br_mux_onehot_rd_data (
          .select(mux_in_rd_data_valid),
          .in(mux_in_rd_data),
          .out(push_rd_data[i])
      );
    end
  end
endmodule
