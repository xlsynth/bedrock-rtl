// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_flops_tile_fpv_monitor #(
    parameter int Depth = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    parameter int NumWritePorts = 1,  // Must be at least 1
    parameter int NumReadPorts = 1,  // Must be at least 1
    // If 1, allow partial writes to the memory using the wr_word_en signal.
    // If 0, only full writes are allowed and wr_word_en is ignored.
    parameter bit EnablePartialWrite = 0,
    // The width of a word in the memory. This is the smallest unit of data that
    // can be written when partial write is enabled.
    // Must be at least 1 and at most Width.
    // Width must be evenly divisible by WordWidth.
    parameter int WordWidth = Width,
    // If 1, then if the read and write ports access the same address on the same cycle,
    // the write data is forwarded directly to the read data with zero delay.
    // If 0, then if the read and write ports access the same address on the same cycle,
    // then read data is the value stored in the memory prior to the write.
    parameter bit EnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset.
    parameter bit EnableReset = 0,
    // If 1, use structured mux2 gates for the read mux instead of relying on synthesis.
    // This is required if write and read clocks are different.
    parameter bit UseStructuredGates = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
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
