// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for partial-write bypass in the 1R1W mock RAM.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w_mock_partial_write_bypass_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int Depth = 4;
  localparam int Width = 16;
  localparam int WordWidth = 8;
  localparam int NumWords = Width / WordWidth;
  localparam int AddressWidth = $clog2(Depth);

  logic [2:0] cycle;
  logic wr_valid;
  logic [AddressWidth-1:0] wr_addr;
  logic [Width-1:0] wr_data;
  logic [NumWords-1:0] wr_word_en;
  logic rd_addr_valid;
  logic [AddressWidth-1:0] rd_addr;
  logic rd_data_valid;
  logic [Width-1:0] rd_data;

  br_ram_flops_1r1w_mock #(
      .Depth(Depth),
      .Width(Width),
      .EnablePartialWrite(1),
      .WordWidth(WordWidth),
      .TileEnableBypass(1),
      .EnableMemReset(1)
  ) dut (
      .wr_clk(clk),
      .wr_rst(rst),
      .wr_valid,
      .wr_addr,
      .wr_data,
      .wr_word_en,
      .rd_clk(clk),
      .rd_rst(rst),
      .rd_addr_valid,
      .rd_addr,
      .rd_data_valid,
      .rd_data
  );

  assign wr_valid = !rst && (cycle == 0 || cycle == 2);
  assign wr_addr = 2'd1;
  assign wr_data = cycle == 0 ? 16'ha55a : 16'hc33c;
  assign wr_word_en = cycle == 0 ? 2'b11 : cycle == 2 ? 2'b01 : '0;
  assign rd_addr_valid = !rst && cycle == 2;
  assign rd_addr = 2'd1;

  `BR_REG(cycle, cycle + 3'd1)

  `BR_ASSERT(partial_write_bypass_merges_words_a,
             cycle == 2 |-> rd_data_valid && rd_data == 16'ha53c)

endmodule : br_ram_flops_1r1w_mock_partial_write_bypass_fpv_repro
