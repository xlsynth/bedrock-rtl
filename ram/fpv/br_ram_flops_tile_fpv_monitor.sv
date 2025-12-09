// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_flops_tile_fpv_monitor #(
    parameter int Depth = 1,
    parameter int Width = 1,
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter bit EnablePartialWrite = 0,
    parameter int WordWidth = Width,
    parameter bit EnableBypass = 0,
    parameter bit EnableReset = 0,
    parameter bit UseStructuredGates = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int NumWords = Width / WordWidth
) (
    input logic                                    wr_clk,
    input logic                                    wr_rst,
    input logic [NumWritePorts-1:0]                wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] wr_addr,
    input logic [NumWritePorts-1:0][    Width-1:0] wr_data,
    input logic [NumWritePorts-1:0][ NumWords-1:0] wr_word_en,


    input logic                                   rd_clk,
    input logic                                   rd_rst,
    input logic [NumReadPorts-1:0]                rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] rd_addr,
    input logic [NumReadPorts-1:0]                rd_data_valid,
    input logic [NumReadPorts-1:0][    Width-1:0] rd_data
);

  br_ram_flops_basic_fv_checker #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .EnablePartialWrite(EnablePartialWrite),
      .WordWidth(WordWidth),
      .EnableBypass(EnableBypass),
      .EnableReset(EnableReset)
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

endmodule : br_ram_flops_tile_fpv_monitor

bind br_ram_flops_tile br_ram_flops_tile_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .EnablePartialWrite(EnablePartialWrite),
    .WordWidth(WordWidth),
    .EnableBypass(EnableBypass),
    .EnableReset(EnableReset),
    .UseStructuredGates(UseStructuredGates),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
