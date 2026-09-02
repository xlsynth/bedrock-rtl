// SPDX-License-Identifier: Apache-2.0

// External RAM contract for the credit/credit shared FIFO controllers. Reads
// observe the array before same-cycle writes, and response valid has the exact
// configured latency. Reset clears the response pipeline, not the memory.

`include "br_asserts.svh"

module br_fifo_credit_fpv_ram #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    input logic [NumWritePorts-1:0] ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ram_wr_addr,
    input logic [NumWritePorts-1:0][Width-1:0] ram_wr_data,

    input logic [NumReadPorts-1:0] ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ram_rd_addr,
    input logic [NumReadPorts-1:0] ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] ram_rd_data
);
  logic [Depth-1:0][Width-1:0] fv_ram;
  logic [NumReadPorts-1:0] fv_rsp_valid;

  always_ff @(posedge clk) begin
    for (int w = 0; w < NumWritePorts; w++) begin
      if (ram_wr_valid[w]) begin
        fv_ram[ram_wr_addr[w]] <= ram_wr_data[w];
      end
    end
  end

  fv_delay #(
      .Width(NumReadPorts),
      .NumStages(RamReadLatency)
  ) fv_valid_delay (
      .clk,
      .rst,
      .in (ram_rd_addr_valid),
      .out(fv_rsp_valid)
  );

  for (genvar r = 0; r < NumReadPorts; r++) begin : gen_read_port
    logic [Width-1:0] fv_rsp_data;

    fv_delay #(
        .Width(Width),
        .NumStages(RamReadLatency)
    ) fv_data_delay (
        .clk,
        .rst,
        .in (fv_ram[ram_rd_addr[r]]),
        .out(fv_rsp_data)
    );

    `BR_ASSUME(ram_response_valid_a, ram_rd_data_valid[r] == fv_rsp_valid[r])
    `BR_ASSUME(ram_response_data_a, ram_rd_data_valid[r] |-> ram_rd_data[r] == fv_rsp_data)
    `BR_ASSERT(read_address_in_range_a, ram_rd_addr_valid[r] |-> ram_rd_addr[r] < Depth)
  end

  for (genvar w = 0; w < NumWritePorts; w++) begin : gen_write_port
    `BR_ASSERT(write_address_in_range_a, ram_wr_valid[w] |-> ram_wr_addr[w] < Depth)
    for (genvar other = w + 1; other < NumWritePorts; other++) begin : gen_other_port
      `BR_ASSERT(no_write_conflict_a,
                 ram_wr_valid[w] && ram_wr_valid[other] |-> ram_wr_addr[w] != ram_wr_addr[other])
    end
  end

endmodule : br_fifo_credit_fpv_ram
