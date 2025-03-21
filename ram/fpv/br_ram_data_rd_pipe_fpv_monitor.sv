// Copyright 2025 The Bedrock-RTL Authors
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

`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_data_rd_pipe_fpv_monitor #(
    // Width of each entry in the RAM. Must be at least 1.
    parameter int Width = 1,
    // Number of tiles along the depth dimension.
    // Must be at least 1 and evenly divide Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width dimension.
    // Must be at least 1 and evenly divide Width.
    parameter int WidthTiles = 1,
    // Number of pipeline stages to join data along the depth dimension.
    // Must be at least 0.
    parameter int DepthStages = 0,
    // Number of pipeline stages to join data along the width dimension.
    // Must be at least 0.
    parameter int WidthStages = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int TileWidth = br_math::ceil_div(Width, WidthTiles),
    localparam int Latency = DepthStages + WidthStages
) (
    input logic                                                 clk,
    input logic                                                 rst,
    input logic [DepthTiles-1:0][WidthTiles-1:0]                tile_valid,
    input logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_data,
    input logic                                                 valid,
    input logic [     Width-1:0]                                data
);

  // ----------FV assumptions----------
  logic [DepthTiles-1:0] depth_tile_valid;

  for (genvar d = 0; d < DepthTiles; d++) begin : gen_asm
    assign depth_tile_valid[d] = |tile_valid[d];
    `BR_ASSUME(tile_valid_depth_onehot_a, |tile_valid |-> $onehot(depth_tile_valid))
    `BR_ASSUME(tile_valid_width_all_one_a, depth_tile_valid[d] |-> &tile_valid[d])
  end

  // ----------FV Modeling Code----------
  logic [WidthTiles-1:0][TileWidth-1:0] depth_tile_data;
  logic [Width-1:0] fv_data;

  always_comb begin
    depth_tile_data = 'd0;
    for (int i = 0; i < DepthTiles; i++) begin
      if (depth_tile_valid[i]) begin
        depth_tile_data = tile_data[i];
      end
    end
  end

  for (genvar w = 0; w < WidthTiles; w++) begin : gen_w
    localparam int Msb = (w + 1) * TileWidth;
    localparam int Lsb = w * TileWidth;
    assign fv_data[Msb-1 : Lsb] = depth_tile_data[w];
  end

  // ----------FV assertions----------
  if (Latency == 0) begin : gen_no_delay
    `BR_ASSERT(valid_integrity_a, |tile_valid == valid)
    `BR_ASSERT(data_integrity_a, valid |-> data == fv_data)
  end else begin : gen_delay
    `BR_ASSERT(valid_integrity_a, ##Latency $past(|tile_valid, Latency) == valid)
    `BR_ASSERT(data_integrity_a, valid |-> data == $past(fv_data, Latency))
  end

endmodule : br_ram_data_rd_pipe_fpv_monitor

bind br_ram_data_rd_pipe br_ram_data_rd_pipe_fpv_monitor #(
    .Width(Width),
    .DepthTiles(DepthTiles),
    .WidthTiles(WidthTiles),
    .DepthStages(DepthStages),
    .WidthStages(WidthStages),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
