// Copyright 2024-2025 The Bedrock-RTL Authors
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

// Bedrock-RTL RAM Read Data Pipeline
//
// TODO(mgottscho): description

`include "br_asserts_internal.svh"
`include "br_tieoff.svh"
`include "br_unused.svh"

module br_ram_data_rd_pipe #(
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
    // Posedge-triggered clock.
    // May not be used if DepthStages == 0 and WidthStages == 0, hence lint waivers.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 clk,
    // Synchronous active-high reset.
    // May not be used if DepthStages == 0 and WidthStages == 0, hence lint waivers.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 rst,
    input  logic [DepthTiles-1:0][WidthTiles-1:0]                tile_valid,
    input  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_data,
    output logic                                                 valid,
    output logic [     Width-1:0]                                data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  // DepthTiles checks
  `BR_ASSERT_STATIC(depth_tiles_gte1_a, DepthTiles >= 1)

  // WidthTiles checks
  `BR_ASSERT_STATIC(width_tiles_gte1_a, WidthTiles >= 1)
  `BR_ASSERT_STATIC(width_tiles_evenly_divides_width_a, (WidthTiles * TileWidth) == Width)

  // DepthStages check
  `BR_ASSERT_STATIC(depth_stages_gte0_a, DepthStages >= 0)

  // WidthStages check
  `BR_ASSERT_STATIC(width_stages_gte0_a, WidthStages >= 0)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  logic [DepthTiles-1:0] depth_tile_valid;
  // ri lint_check_waive IFDEF_CODE
  for (genvar d = 0; d < DepthTiles; d++) begin : gen_checks_d
    assign depth_tile_valid[d] = |tile_valid[d];
    `BR_ASSERT_INTG(widthwise_tile_valid_lockstep_a, tile_valid[d] == '0 || tile_valid[d] == '1)
  end
  `BR_ASSERT_INTG(depthwise_tile_valid_onehot0_a, $onehot0(depth_tile_valid))
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // We only use some of the valids along the width dimension.
  // ri lint_check_waive INEFFECTIVE_NET
  logic [DepthTiles-1:0][WidthTiles-1:0]                tile_valid_q;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_data_q;

  logic [DepthTiles-1:0]                                row_valid;
  logic [DepthTiles-1:0][     Width-1:0]                row_data;

  logic [DepthTiles-1:0]                                row_valid_q;
  logic [DepthTiles-1:0][     Width-1:0]                row_data_q;

  for (genvar d = 0; d < DepthTiles; d++) begin : gen_d
    // Step 0: Concat tile data along width dimension.
    //
    // We register WidthStages >= 0 number of times before concatenating.
    // WidthStages == 0 and WidthStages == 1 are useful but >1 is of presently
    // dubious value (unless we later choose to implement a pipelined concat tree).
    // But supporting >1 is easy and doesn't hurt anything.
    for (genvar w = 0; w < WidthTiles; w++) begin : gen_w
      br_delay_valid #(
          .Width(TileWidth),
          .NumStages(WidthStages),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_delay_valid_w (
          .clk,
          .rst,
          .in_valid(tile_valid[d][w]),
          .in(tile_data[d][w]),
          .out_valid(tile_valid_q[d][w]),
          .out(tile_data_q[d][w]),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );
    end

    // All the width tile valids in a row are required to be in lockstep, so just pick the middle index.
    localparam int WidthMiddleTile = br_math::floor_div(WidthTiles, 2);
    assign row_valid[d] = tile_valid_q[d][WidthMiddleTile];

    // Annoying unused conditions
    localparam int NumUnusedWidthTileValidMsbs = (WidthTiles - WidthMiddleTile) - 1;
    localparam int NumUnusedWidthTileValidLsbs = WidthMiddleTile;
    if (NumUnusedWidthTileValidMsbs > 0) begin : gen_width_upper_tile_valid_q_unused
      `BR_UNUSED_NAMED(tile_valid_q_msbs, tile_valid_q[d][WidthTiles-1:WidthMiddleTile+1])
    end
    if (NumUnusedWidthTileValidLsbs > 0) begin : gen_width_lower_tile_valid_q_unused
      `BR_UNUSED_NAMED(tile_valid_q_lsbs, tile_valid_q[d][WidthMiddleTile-1:0])
    end
    // Because WidthTiles * TileWidth == Width, we can just directly assign.
    assign row_data[d] = tile_data_q[d];

    // Step 1: Mux tile data along depth dimension (at most one depth row can be valid).
    //
    // We register DepthStages >= 0 number of times before muxing.
    // DepthStages == 0 and DepthStages == 1 are useful but >1 is of presently
    // dubious value (unless we later choose to implement a pipelined mux tree).
    // But supporting >1 is easy and doesn't hurt anything.
    br_delay_valid #(
        .Width(Width),
        .NumStages(DepthStages),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_delay_valid_d (
        .clk,
        .rst,
        .in_valid(row_valid[d]),
        .in(row_data[d]),
        .out_valid(row_valid_q[d]),
        .out(row_data_q[d]),
        .out_valid_stages(),  // unused
        .out_stages()  // unused
    );
  end

  // At most one depthtile can be valid, so OR them.
  assign valid = |row_valid_q;

  if (DepthTiles > 1) begin : gen_mux
    br_mux_onehot #(
        .NumSymbolsIn(DepthTiles),
        .SymbolWidth (Width)
    ) br_mux_onehot (
        .select(row_valid_q),
        .in(row_data_q),
        .out(data)
    );
  end else begin : gen_no_mux
    assign data = row_data_q[0];
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (Latency > 0) begin : gen_stages_gt0
    for (genvar d = 0; d < DepthTiles; d++) begin : gen_d_impl_checks
      `BR_ASSERT_IMPL(propagation_a,
                      tile_valid[d] |-> ##Latency valid && data == $past(tile_data[d], Latency))
    end
    `BR_ASSERT_IMPL(causality_a, valid |-> $past(|tile_valid, Latency))

  end else begin : gen_stages_eq0
    for (genvar d = 0; d < DepthTiles; d++) begin : gen_d_impl_checks
      `BR_ASSERT_IMPL(propagation_a, tile_valid[d] |-> valid && data == tile_data[d])
    end
    `BR_ASSERT_IMPL(causality_a, valid |-> |tile_valid)
  end

  // Rely on submodule implementation checks

endmodule : br_ram_data_rd_pipe
