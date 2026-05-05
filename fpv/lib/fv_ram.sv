// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module fv_ram #(
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

  `BR_ASSERT_STATIC(num_write_ports_gte_1_a, NumWritePorts >= 1)
  `BR_ASSERT_STATIC(num_read_ports_gte_1_a, NumReadPorts >= 1)
  `BR_ASSERT_STATIC(depth_gte_1_a, Depth >= 1)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)
  `BR_ASSERT_STATIC(ram_read_latency_gte_0_a, RamReadLatency >= 0)

  // ----------FV Modeling Code----------
  logic [Depth-1:0][Width-1:0] fv_ram_data;
  logic [Depth-1:0][Width-1:0] fv_ram_data_next;

  always_comb begin
    fv_ram_data_next = fv_ram_data;
    for (int w = 0; w < NumWritePorts; w++) begin
      if (ram_wr_valid[w]) begin
        fv_ram_data_next[ram_wr_addr[w]] = ram_wr_data[w];
      end
    end
  end
  `BR_REGN(fv_ram_data, fv_ram_data_next)

  // ----------FV assertions----------
  if (NumWritePorts > 1) begin : gen_write_conflict_checks
    for (genvar porta = 0; porta < (NumWritePorts - 1); porta++) begin : gen_write_conflict_a
      for (genvar portb = porta + 1; portb < NumWritePorts; portb++) begin : gen_write_conflict_b
        `BR_ASSERT(no_write_conflict_a,
                   (ram_wr_valid[porta] && ram_wr_valid[portb]) |->
                       ram_wr_addr[porta] != ram_wr_addr[portb])
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

endmodule : fv_ram
