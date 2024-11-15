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
// Heavily parameterized for tiling and pipeline configurations.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    // Number of tiles along the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int WidthTiles = 1,
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
    parameter bit TileEnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset. Otherwise, they are undefined until
    // written for the first time.
    parameter bit EnableMemReset = 0,
    localparam int AddressWidth = $clog2(Depth),
    // ri lint_check_waive PARAM_NOT_USED
    localparam int WriteLatency = AddressDepthStages + 1,
    localparam int ReadLatency = AddressDepthStages + ReadDataDepthStages + ReadDataWidthStages,
    localparam int ReadAfterWriteHazardLatency = TileEnableBypass ? 0 : 1
) (
    // Posedge-triggered clock.
    input  logic                    clk,
    // Synchronous active-high reset.
    // Reset is not used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                    rst,
    input  logic                    wr_valid,
    input  logic [AddressWidth-1:0] wr_addr,
    input  logic [       Width-1:0] wr_data,
    input  logic                    rd_addr_valid,
    input  logic [AddressWidth-1:0] rd_addr,
    output logic                    rd_data_valid,
    output logic [       Width-1:0] rd_data
);

  localparam int TileDepth = br_math::ceil_div(Depth, DepthTiles);
  localparam int TileWidth = br_math::ceil_div(Width, WidthTiles);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
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
  `BR_ASSERT_INTG(wr_addr_in_range_a, wr_valid |-> wr_addr < Depth)
  `BR_ASSERT_INTG(rd_addr_in_range_a, rd_addr_valid |-> rd_addr < Depth)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int TileAddressWidth = $clog2(TileDepth);

  logic [DepthTiles-1:0] tile_wr_valid;
  logic [DepthTiles-1:0][TileAddressWidth-1:0] tile_wr_addr;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_wr_data;

  logic [DepthTiles-1:0] tile_rd_addr_valid;
  logic [DepthTiles-1:0][TileAddressWidth-1:0] tile_rd_addr;
  logic [DepthTiles-1:0][WidthTiles-1:0] tile_rd_data_valid;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_rd_data;

  // Write pipeline (address + data)
  br_ram_addr_decoder #(
      .Depth(Depth),
      .DataWidth(Width),
      .Tiles(DepthTiles),
      .Stages(AddressDepthStages)
  ) br_ram_addr_decoder_wr (
      .clk,
      .rst,
      .in_valid (wr_valid),
      .in_addr  (wr_addr),
      .in_data  (wr_data),
      .out_valid(tile_wr_valid),
      .out_addr (tile_wr_addr),
      .out_data (tile_wr_data)
  );

  // Read address pipeline
  br_ram_addr_decoder #(
      .Depth (Depth),
      .Tiles (DepthTiles),
      .Stages(AddressDepthStages)
  ) br_ram_addr_decoder_rd (
      .clk,
      .rst,
      .in_valid(rd_addr_valid),
      .in_addr(rd_addr),
      .in_data(1'b0),  // unused
      .out_valid(tile_rd_addr_valid),
      .out_addr(tile_rd_addr),
      .out_data()  // unused
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
          .rd_data_valid(tile_rd_data_valid[r][c]),
          .rd_data(tile_rd_data[r][c])
      );
    end
  end

  // Read data pipeline
  br_ram_data_rd_pipe #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles),
      .DepthStages(ReadDataDepthStages),
      .WidthStages(ReadDataWidthStages)
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
  `BR_ASSERT_IMPL(read_latency_a, rd_addr_valid |-> ##ReadLatency rd_data_valid)

  if (ReadAfterWriteHazardLatency == 0) begin : gen_hazard0_checks
    if (ReadLatency > 0) begin : gen_readlat_gt0
      `BR_ASSERT_IMPL(read_write_hazard_gets_new_data_a,
                      wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          ##ReadLatency rd_data_valid && rd_data == $past(
                          wr_data, ReadLatency
                      ))
    end else begin : gen_readlat_eq0
      `BR_ASSERT_IMPL(read_write_hazard_gets_new_data_a,
                      wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          rd_data_valid && (rd_data == wr_data))
    end
  end else begin : gen_hazard1_checks
    if (ReadLatency > 0) begin : gen_readlat_gt0
      `BR_COVER_IMPL(read_write_hazard_gets_old_data_c,
                     (wr_valid && rd_addr_valid && (wr_addr == rd_addr)) ##ReadLatency
          (rd_data_valid && rd_data != $past(
                         wr_data, ReadLatency
                     )))
    end else begin : gen_readlat_eq0
      `BR_COVER_IMPL(
          read_write_hazard_gets_old_data_c,
          (wr_valid && rd_addr_valid && (wr_addr == rd_addr)) && rd_data_valid && (rd_data != $past(
          wr_data)))
    end
  end

  // Rely on submodule implementation checks

endmodule : br_ram_flops_1r1w
