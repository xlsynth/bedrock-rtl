// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_flops_fpv_monitor #(
    parameter int NumReadPorts = 1,  // Number of read ports. Must be at least 1.
    parameter int NumWritePorts = 1,  // Number of write ports. Must be at least 1.
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    // Number of tiles along the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int WidthTiles = 1,
    // If 1, allow partial writes to the memory using the wr_word_en signal.
    // If 0, only full writes are allowed and wr_word_en is ignored.
    parameter bit EnablePartialWrite = 0,
    // The width of a word in the memory. This is the smallest unit of data that
    // can be written when partial write is enabled.
    // Must be at least 1 and at most (Width / WidthTiles).
    // Must be evenly divisible by WidthTiles.
    // Width must be evenly divisible by WordWidth.
    parameter int WordWidth = Width / WidthTiles,
    // Number of pipeline register stages inserted along the write address and read address paths
    // in the depth dimension. Must be at least 0.
    parameter int AddressDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the depth dimension.
    // Must be at least 0.
    parameter int ReadDataDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the width dimension.
    // Must be at least 0.
    parameter int ReadDataWidthStages = 0,
    // If 1, then each memory tile has a read-after-write hazard latency of 0 cycles, i.e.,
    // if the tile read and write address are valid and equal on the same cycle then the tile
    // read data equals the tile write data.
    // If 0, then each memory tile has a read-after-write hazard latency of 1 cycle, i.e.,
    // a read cannot observe previously written data unless the read address is issued at least
    // one cycle after the write.
    // Bypassing is only permissible if the read and write clocks are the same.
    parameter bit TileEnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset. Otherwise, they are undefined until
    // written for the first time.
    parameter bit EnableMemReset = 0,
    // If 1, use structured mux2 gates for the read mux instead of relying on synthesis.
    // This is required if write and read clocks are different.
    parameter bit UseStructuredGates = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddressWidth = br_math::clamped_clog2(Depth),
    localparam int NumWords = Width / WordWidth,
    // Write latency in units of wr_clk cycles
    // ri lint_check_waive PARAM_NOT_USED
    localparam int WriteLatency = AddressDepthStages + 1,
    // Read latency in units of rd_clk cycles. Only used for assertions.
    // ri lint_check_waive PARAM_NOT_USED
    localparam int ReadLatency = AddressDepthStages + ReadDataDepthStages + ReadDataWidthStages
) (
    input logic                                       wr_clk,
    input logic                                       wr_rst,
    input logic [NumWritePorts-1:0]                   wr_valid,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] wr_addr,
    input logic [NumWritePorts-1:0][       Width-1:0] wr_data,
    input logic [NumWritePorts-1:0][    NumWords-1:0] wr_word_en,

    input logic                                      rd_clk,
    input logic                                      rd_rst,
    input logic [NumReadPorts-1:0]                   rd_addr_valid,
    input logic [NumReadPorts-1:0][AddressWidth-1:0] rd_addr,
    input logic [NumReadPorts-1:0]                   rd_data_valid,
    input logic [NumReadPorts-1:0][       Width-1:0] rd_data
);

  br_ram_flops_basic_fv_checker #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .EnablePartialWrite(EnablePartialWrite),
      .WordWidth(WordWidth),
      .EnableBypass(TileEnableBypass),
      .EnableReset(EnableMemReset),
      .WriteLatency(AddressDepthStages),
      .ReadLatency(ReadDataDepthStages + ReadDataWidthStages)
  ) fv_checker (
      .wr_clk,
      .wr_rst,
      .wr_valid,
      .wr_addr,
      .wr_data,
      .wr_word_en,
      .rd_clk,
      .rd_rst,
      .rd_addr_valid,
      .rd_addr,
      .rd_data_valid,
      .rd_data
  );

endmodule : br_ram_flops_fpv_monitor

bind br_ram_flops br_ram_flops_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .DepthTiles(DepthTiles),
    .WidthTiles(WidthTiles),
    .EnablePartialWrite(EnablePartialWrite),
    .WordWidth(WordWidth),
    .AddressDepthStages(AddressDepthStages),
    .ReadDataDepthStages(ReadDataDepthStages),
    .ReadDataWidthStages(ReadDataWidthStages),
    .TileEnableBypass(TileEnableBypass),
    .EnableMemReset(EnableMemReset),
    .UseStructuredGates(UseStructuredGates),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
