// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w_mock_fpv_monitor #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1,
    parameter bit EnablePartialWrite = 0,
    parameter int WordWidth = Width / WidthTiles,
    parameter int AddressDepthStages = 0,
    parameter int ReadDataDepthStages = 0,
    parameter int ReadDataWidthStages = 0,
    parameter bit TileEnableBypass = 0,
    parameter bit EnableMemReset = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddressWidth = $clog2(Depth),
    localparam int NumWords = br_math::ceil_div(Width, WordWidth)
) (
    input logic                    wr_clk,
    input logic                    wr_rst,
    input logic                    wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [       Width-1:0] wr_data,
    input logic [    NumWords-1:0] wr_word_en,

    input logic                    rd_clk,
    input logic                    rd_rst,
    input logic                    rd_addr_valid,
    input logic [AddressWidth-1:0] rd_addr,
    input logic                    rd_data_valid,
    input logic [       Width-1:0] rd_data
);

  br_ram_flops_basic_fv_checker #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(1),
      .NumReadPorts(1),
      .EnablePartialWrite(EnablePartialWrite),
      .WordWidth(WordWidth),
      .EnableBypass(TileEnableBypass),
      .EnableReset(EnableMemReset),
      .WriteLatency(AddressDepthStages),
      .ReadLatency(ReadDataDepthStages + ReadDataWidthStages)
  ) fv_checker (
      .wr_clk,
      .wr_rst,
      .wr_valid(wr_valid),
      .wr_addr(wr_addr),
      .wr_data(wr_data),
      .wr_word_en(wr_word_en),
      .rd_clk,
      .rd_rst,
      .rd_addr_valid(rd_addr_valid),
      .rd_addr(rd_addr),
      .rd_data_valid(rd_data_valid),
      .rd_data(rd_data)
  );

endmodule : br_ram_flops_1r1w_mock_fpv_monitor

bind br_ram_flops_1r1w_mock br_ram_flops_1r1w_mock_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .DepthTiles(DepthTiles),
    .WidthTiles(WidthTiles),
    .EnablePartialWrite(EnablePartialWrite),
    .WordWidth(WordWidth),
    .AddressDepthStages(AddressDepthStages),
    .ReadDataDepthStages(ReadDataDepthStages),
    .ReadDataWidthStages(ReadDataWidthStages),
    .TileEnableBypass(TileEnableBypass),
    .EnableMemReset(EnableMemReset),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
