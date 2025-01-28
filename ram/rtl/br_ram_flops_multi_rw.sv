// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Flop-RAM (multi-read/multi-write)
//
// A multi-read/multi-write flop-based RAM
// that is constructed out of pipelined tiles.
// Heavily parameterized for tiling and pipeline configurations.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_ram_flops_multi_rw #(
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
    localparam int AddressWidth = $clog2(Depth),
    localparam int NumWords = Width / WordWidth,
    // Write latency in units of wr_clk cycles
    // ri lint_check_waive PARAM_NOT_USED
    localparam int WriteLatency = AddressDepthStages + 1,
    // Read latency in units of rd_clk cycles
    localparam int ReadLatency = AddressDepthStages + ReadDataDepthStages + ReadDataWidthStages
) (
    // Write-clock signals
    // Posedge-triggered clock.
    input logic                                       wr_clk,
    // Synchronous active-high reset.
    // Reset is not used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic                                       wr_rst,
    input logic [NumWritePorts-1:0]                   wr_valid,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] wr_addr,
    input logic [NumWritePorts-1:0][       Width-1:0] wr_data,
    input logic [NumWritePorts-1:0][    NumWords-1:0] wr_word_en,

    // Read-clock signals
    // Posedge-triggered clock.
    // The clock may not be used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                      rd_clk,
    // Synchronous active-high reset.
    // Reset is not used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                      rd_rst,
    input  logic [NumReadPorts-1:0]                   rd_addr_valid,
    input  logic [NumReadPorts-1:0][AddressWidth-1:0] rd_addr,
    output logic [NumReadPorts-1:0]                   rd_data_valid,
    output logic [NumReadPorts-1:0][       Width-1:0] rd_data
);

  localparam int TileDepth = br_math::ceil_div(Depth, DepthTiles);
  localparam int TileWidth = br_math::ceil_div(Width, WidthTiles);
  localparam int TileNumWords = br_math::ceil_div(NumWords, WidthTiles);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_write_ports_gte1_a, NumWritePorts >= 1)
  `BR_ASSERT_STATIC(num_read_ports_gte1_a, NumReadPorts >= 1)
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  // DepthTiles checks
  `BR_ASSERT_STATIC(depth_tiles_gte1_a, DepthTiles >= 1)
  `BR_ASSERT_STATIC(depth_tiles_evenly_divides_depth_a, (DepthTiles * TileDepth) == Depth)

  // WidthTiles checks
  `BR_ASSERT_STATIC(width_tiles_gte1_a, WidthTiles >= 1)
  `BR_ASSERT_STATIC(width_tiles_evenly_divides_width_a, (WidthTiles * TileWidth) == Width)

  // Address stages checks
  `BR_ASSERT_STATIC(address_depth_stages_gte0_a, AddressDepthStages >= 0)

  // Read data stages checks
  `BR_ASSERT_STATIC(read_data_depth_stages_gte0_a, ReadDataDepthStages >= 0)
  `BR_ASSERT_STATIC(read_data_width_stages_gte0_a, ReadDataWidthStages >= 0)

  // Address range checks
  `BR_ASSERT_CR_INTG(wr_addr_in_range_a, wr_valid |-> wr_addr < Depth, wr_clk, wr_rst)
  `BR_ASSERT_CR_INTG(rd_addr_in_range_a, rd_addr_valid |-> rd_addr < Depth, rd_clk, rd_rst)

  if (EnablePartialWrite) begin : gen_partial_write_intg_checks
    `BR_ASSERT_STATIC(word_width_in_range_a, (WordWidth >= 1) && (WordWidth <= TileWidth))
    `BR_ASSERT_STATIC(num_words_div_width_tiles_a, (NumWords % WidthTiles) == 0)
    `BR_ASSERT_STATIC(tile_width_div_word_width_a, (TileWidth % WordWidth) == 0)
  end

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int TileAddressWidth = $clog2(TileDepth);

  logic [DepthTiles-1:0][NumWritePorts-1:0] tile_wr_valid;
  logic [DepthTiles-1:0][NumWritePorts-1:0][TileAddressWidth-1:0] tile_wr_addr;
  logic [DepthTiles-1:0][WidthTiles-1:0][NumWritePorts-1:0][TileWidth-1:0] tile_wr_data;
  logic [DepthTiles-1:0][WidthTiles-1:0][NumWritePorts-1:0][TileNumWords-1:0] tile_wr_word_en;

  logic [DepthTiles-1:0][NumReadPorts-1:0] tile_rd_addr_valid;
  logic [DepthTiles-1:0][NumReadPorts-1:0][TileAddressWidth-1:0] tile_rd_addr;
  logic [DepthTiles-1:0][WidthTiles-1:0][NumReadPorts-1:0] tile_rd_data_valid;
  logic [DepthTiles-1:0][WidthTiles-1:0][NumReadPorts-1:0][TileWidth-1:0] tile_rd_data;

  for (genvar wport = 0; wport < NumWritePorts; wport++) begin : gen_write_decoder
    logic [DepthTiles-1:0] decoded_wr_valid;
    logic [DepthTiles-1:0][TileAddressWidth-1:0] decoded_wr_addr;
    logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] decoded_wr_data;
    logic [DepthTiles-1:0][WidthTiles-1:0][TileNumWords-1:0] decoded_wr_word_en;

    // Write pipeline (address + data)
    if (EnablePartialWrite) begin : gen_partial_write_addr_decoder
      localparam int DecoderDataWidth = Width + NumWords;
      logic [DecoderDataWidth-1:0] decoder_in_data;
      logic [DepthTiles-1:0][DecoderDataWidth-1:0] decoder_out_data;

      assign decoder_in_data = {wr_data[wport], wr_word_en[wport]};

      br_ram_addr_decoder #(
          .Depth(Depth),
          .DataWidth(DecoderDataWidth),
          .Tiles(DepthTiles),
          .Stages(AddressDepthStages),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_ram_addr_decoder_wr (
          .clk(wr_clk),  // ri lint_check_waive SAME_CLOCK_NAME
          .rst(wr_rst),
          .in_valid(wr_valid[wport]),
          .in_addr(wr_addr[wport]),
          .in_data(decoder_in_data),
          .out_valid(decoded_wr_valid),
          .out_addr(decoded_wr_addr),
          .out_data(decoder_out_data)
      );

      for (genvar i = 0; i < DepthTiles; i++) begin : gen_tile_wr_data_and_word_en
        assign {decoded_wr_data[i], decoded_wr_word_en[i]} = decoder_out_data[i];
      end
    end else begin : gen_full_write_addr_decoder
      br_ram_addr_decoder #(
          .Depth(Depth),
          .DataWidth(Width),
          .Tiles(DepthTiles),
          .Stages(AddressDepthStages),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_ram_addr_decoder_wr (
          .clk(wr_clk),  // ri lint_check_waive SAME_CLOCK_NAME
          .rst(wr_rst),
          .in_valid(wr_valid[wport]),
          .in_addr(wr_addr[wport]),
          .in_data(wr_data[wport]),
          .out_valid(decoded_wr_valid),
          .out_addr(decoded_wr_addr),
          .out_data(decoded_wr_data)
      );

      `BR_UNUSED(wr_word_en[wport])
      assign decoded_wr_word_en = '1;
    end

    for (genvar r = 0; r < DepthTiles; r++) begin : gen_tile_write_depth
      assign tile_wr_valid[r][wport] = decoded_wr_valid[r];
      assign tile_wr_addr[r][wport]  = decoded_wr_addr[r];
      for (genvar c = 0; c < WidthTiles; c++) begin : gen_tile_write_width
        assign tile_wr_data[r][c][wport] = decoded_wr_data[r][c];
        assign tile_wr_word_en[r][c][wport] = decoded_wr_word_en[r][c];
      end
    end
  end

  for (genvar rport = 0; rport < NumReadPorts; rport++) begin : gen_read_decoder
    logic [DepthTiles-1:0] decoded_rd_addr_valid;
    logic [DepthTiles-1:0][TileAddressWidth-1:0] decoded_rd_addr;

    // Read address pipeline
    br_ram_addr_decoder #(
        .Depth(Depth),
        .Tiles(DepthTiles),
        .Stages(AddressDepthStages),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_ram_addr_decoder_rd (
        .clk(rd_clk),  // ri lint_check_waive SAME_CLOCK_NAME
        .rst(rd_rst),
        .in_valid(rd_addr_valid[rport]),
        .in_addr(rd_addr[rport]),
        .in_data(1'b0),  // unused
        .out_valid(decoded_rd_addr_valid),
        .out_addr(decoded_rd_addr),
        .out_data()  // unused
    );

    for (genvar i = 0; i < DepthTiles; i++) begin : gen_tile_read
      assign tile_rd_addr_valid[i][rport] = decoded_rd_addr_valid[i];
      assign tile_rd_addr[i][rport] = decoded_rd_addr[i];
    end
  end

  // Memory tiles
  for (genvar r = 0; r < DepthTiles; r++) begin : gen_row
    for (genvar c = 0; c < WidthTiles; c++) begin : gen_col
      br_ram_flops_1r1w_tile #(
          .Depth(TileDepth),
          .Width(TileWidth),
          .WordWidth(WordWidth),
          .EnableBypass(TileEnableBypass),
          .EnableReset(EnableMemReset),
          .UseStructuredGates(UseStructuredGates),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_ram_flops_1r1w_tile (
          .wr_clk,
          .wr_rst,
          .wr_valid(tile_wr_valid[r]),
          .wr_addr(tile_wr_addr[r]),
          .wr_data(tile_wr_data[r][c]),
          .wr_word_en(tile_wr_word_en[r][c]),
          .rd_clk,
          .rd_rst,
          .rd_addr_valid(tile_rd_addr_valid[r]),
          .rd_addr(tile_rd_addr[r]),
          .rd_data_valid(tile_rd_data_valid[r][c]),
          .rd_data(tile_rd_data[r][c])
      );
    end
  end

  for (genvar rport = 0; rport < NumReadPorts; rport++) begin : gen_read_data_pipe
    logic [DepthTiles-1:0][WidthTiles-1:0] pipe_rd_data_valid;
    logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] pipe_rd_data;

    for (genvar r = 0; r < DepthTiles; r++) begin : gen_pipe_rd_data_depth
      for (genvar c = 0; c < WidthTiles; c++) begin : gen_pipe_rd_data_width
        assign pipe_rd_data_valid[r][c] = tile_rd_data_valid[r][c][rport];
        assign pipe_rd_data[r][c] = tile_rd_data[r][c][rport];
      end
    end

    // Read data pipeline
    br_ram_data_rd_pipe #(
        .Width(Width),
        .DepthTiles(DepthTiles),
        .WidthTiles(WidthTiles),
        .DepthStages(ReadDataDepthStages),
        .WidthStages(ReadDataWidthStages),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_ram_data_rd_pipe (
        .clk(rd_clk),  // ri lint_check_waive SAME_CLOCK_NAME
        .rst(rd_rst),
        .tile_valid(pipe_rd_data_valid),
        .tile_data(pipe_rd_data),
        .valid(rd_data_valid[rport]),
        .data(rd_data[rport])
    );
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(read_latency_a, rd_addr_valid |-> ##ReadLatency rd_data_valid, rd_clk, rd_rst)

  if (TileEnableBypass) begin : gen_bypass_checks
    if (ReadLatency > 0) begin : gen_readlat_gt0
      `BR_ASSERT_CR_IMPL(read_write_hazard_gets_new_data_a,
                         wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          ##ReadLatency rd_data_valid && rd_data == $past(
                             wr_data, ReadLatency
                         ),
                         rd_clk, rd_rst)
    end else begin : gen_readlat_eq0
      `BR_ASSERT_CR_IMPL(read_write_hazard_gets_new_data_a,
                         wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          rd_data_valid && (rd_data == wr_data),
                         rd_clk, rd_rst)
    end
  end

  `BR_ASSERT_FINAL(final_not_rd_data_valid_a, !rd_data_valid)

endmodule : br_ram_flops_multi_rw
