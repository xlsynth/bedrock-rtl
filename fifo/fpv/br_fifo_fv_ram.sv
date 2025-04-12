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

// Bedrock-RTL Shared Dynamic Multi-FIFO Controller (Push Valid/Ready Interface) FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_fv_ram #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Data RAM Ports
    input logic [NumWritePorts-1:0] ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ram_wr_addr,
    input logic [NumWritePorts-1:0][Width-1:0] ram_wr_data,

    input logic [NumReadPorts-1:0] ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ram_rd_addr,
    input logic [NumReadPorts-1:0] ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] ram_rd_data
);

  // ----------FV Modeling Code----------
  logic [Depth-1:0][Width-1:0] fv_ram_data;

  always_ff @(posedge clk) begin
    for (int w = 0; w < NumWritePorts; w++) begin
      if (ram_wr_valid[w]) begin
        fv_ram_data[ram_wr_addr[w]] <= ram_wr_data[w];
      end
    end
  end

  // ----------FV assumptions----------
  for (genvar r = 0; r < NumReadPorts; r++) begin : gen_asm
    if (RamReadLatency == 0) begin : gen_lat0
      `BR_ASSUME(ram_rd_data_a, ram_rd_data[r] == fv_ram_data[ram_rd_addr[r]])
      `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid[r] == ram_rd_addr_valid[r])
    end else begin : gen_lat_non0
      `BR_ASSUME(ram_rd_data_a, ram_rd_data[r] == $past(fv_ram_data[ram_rd_addr[r]], RamReadLatency
                 ))
      `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid[r] == $past(
                 ram_rd_addr_valid[r], RamReadLatency))
    end
  end

endmodule
