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

// Bedrock-RTL Flop-RAM (1R1W)
//
// A one-read/one-write (1R1W, also known as pseudo-dual-port) flop-based RAM
// that is constructed out of pipelined tiles.
//
// Parameterized write, read, and read-after-write hazard latencies.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    // Number of tiles along the depth (address) dimension. Must be a positive power-of-2
    // and less than or equal to Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be a positive power-of-2
    // and less than or equal to Width.
    parameter int WidthTiles = 1,
    // Number of pipeline register stages inserted along the write address and read address paths.
    // Must be at least 0 and less than or equal to $clog2(DepthTiles).
    parameter int AddressStages = 0,
    // Number of pipeline register stages inserted along the read data path.
    // Must be at least 0 and less than or equal to $clog2(WidthTiles).
    parameter int ReadDataStages = 0,
    // If 1, then each memory tile has a read-after-write hazard latency of 0 cycles, i.e.,
    // if the tile read and write address are valid and equal on the same cycle then the tile
    // read data equals the tile write data.
    // If 0, then each memory tile has a read-after-write hazard latency of 1 cycle, i.e.,
    // a read cannot observe previously written data unless the read address is issued at least
    // one cycle after the write.
    parameter bit TileEnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset. Otherwise, they are undefined until
    // written for the first time.
    parameter bit EnableMemReset = 0,
    localparam int WriteLatency = AddressStages + 1,
    localparam int ReadLatency = AddressStages + ReadDataStages,
    localparam int ReadAfterWriteHazardLatency = TileEnableBypass ? 0 : 1,
    localparam int AddressWidth = $clog2(Depth)
) (
    // Posedge-triggered clock.
    input  logic                    clk,
    // Synchronous active-high reset.
    input  logic                    rst,
    input  logic                    wr_valid,
    input  logic [AddressWidth-1:0] wr_addr,
    input  logic [       Width-1:0] wr_data,
    input  logic                    rd_addr_valid,
    input  logic [AddressWidth-1:0] rd_addr,
    output logic                    rd_data_valid,
    output logic [       Width-1:0] rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  // DepthTiles checks
  `BR_ASSERT_STATIC(depth_tiles_gt0_a, DepthTiles > 0)
  `BR_ASSERT_STATIC(depth_tiles_power_of_2_a, br_math::is_power_of_2(DepthTiles))
  `BR_ASSERT_STATIC(depth_tiles_lte_depth_a, DepthTiles <= Depth)

  // WidthTiles checks
  `BR_ASSERT_STATIC(bitwidth_tiles_gt0_a, WidthTiles > 0)
  `BR_ASSERT_STATIC(bitwidth_tiles_power_of_2_a, br_math::is_power_of_2(WidthTiles))
  `BR_ASSERT_STATIC(bitwidth_tiles_lte_bitwidth_a, WidthTiles <= Width)

  // AddressStages checks
  `BR_ASSERT_STATIC(address_stages_gte0_a, AddressStages >= 0)
  `BR_ASSERT_STATIC(address_stages_lte_clog2_depth_tiles_a, AddressStages <= $clog2(DepthTiles))

  // ReadDataStages checks
  `BR_ASSERT_STATIC(read_data_stages_gte0_a, ReadDataStages >= 0)
  `BR_ASSERT_STATIC(read_data_stages_lte_clog2_depth_tiles_a, ReadDataStages <= $clog2(WidthTiles))

  // TODO(mgottscho): write more
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int TileDepth = br_math::ceil_div(Depth, DepthTiles);
  localparam int TileWidth = br_math::ceil_div(Width, WidthTiles);
  localparam int TileAddressWidth = $clog2(TileDepth);

  logic [DepthTiles-1:0] tile_wr_valid;
  logic [DepthTiles-1:0][TileAddressWidth-1:0] tile_wr_addr;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_wr_data;

  logic [DepthTiles-1:0] tile_rd_addr_valid;
  logic [DepthTiles-1:0][TileAddressWidth-1:0] tile_rd_addr;
  logic [DepthTiles-1:0] tile_rd_data_valid;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_rd_data;

  // Write pipeline (address + data)
  br_ram_addr_decoder_tree #(
      .Depth(Depth),
      .DataWidth(Width),
      .Tiles(DepthTiles)
  ) br_ram_addr_decoder_tree_wr (
      .clk,
      .rst,
      .addr_valid(wr_valid),
      .addr(wr_addr),
      .data(wr_data),
      .tile_valid(tile_wr_valid),
      .tile_addr(tile_wr_addr),
      .tile_data(tile_wr_data)
  );

  // Read address pipeline
  br_ram_addr_decoder_tree #(
      .Depth(Depth),
      .Tiles(DepthTiles)
  ) br_ram_addr_decoder_tree_rd (
      .clk,
      .rst,
      .valid(rd_addr_valid),
      .addr(rd_addr),
      .data('0),  // unused
      .tile_addr_valid(tile_rd_addr_valid),
      .tile_addr(tile_rd_addr),
      .tile_data()  // unused
  );

  // Memory tiles
  for (genvar r = 0; r < DepthTiles; r++) begin : gen_row
    for (genvar c = 0; c < WidthTiles; c++) begin : gen_col
      br_ram_flops_1r1w_tile #(
          .Depth(TileDepth),
          .Width(TileWidth),
          .EnableBypass(TileEnableBypass),
          .EnableReset(EnableMemReset)
      ) br_ram_flops_1r1w_tile (
          .clk,
          .rst,
          .wr_valid(tile_wr_valid[r]),
          .wr_addr(tile_wr_addr[r]),
          .wr_data(tile_wr_data[r][c]),
          .rd_addr_valid(tile_rd_addr_valid[r]),
          .rd_addr(tile_rd_addr[r]),
          .rd_data_valid(tile_rd_data_valid[r]),
          .rd_data(tile_rd_data[r][c])
      );
    end
  end

  // Read data pipeline
  br_ram_data_rd_pipe #(
      .Depth(Depth),
      .DataWidth(Width),
      .Tiles(DepthTiles),
      .Stages(ReadDataStages)
  ) br_ram_data_rd_pipe (
      .clk,
      .rst,
      .tile_valid(tile_rd_data_valid),
      .tile_data(tile_rd_data),
      .valid(rd_data_valid),
      .data(rd_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(read_latency_A, rd_addr_valid |-> ##ReadLatency rd_data_valid)

  // TODO(mgottscho): Write more
  // Rely on submodule implementation checks

endmodule : br_ram_flops_1r1w
