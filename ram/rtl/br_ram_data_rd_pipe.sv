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

// Bedrock-RTL RAM Read Data Pipeline
//
// TODO(mgottscho): description

`include "br_asserts_internal.svh"
`include "br_tieoff.svh"
`include "br_unused.svh"

module br_ram_data_rd_pipe #(
    // Number of entries in the RAM. Must be at least 2.
    parameter int Depth = 2,
    // Must be at least 1.
    parameter int Width = 1,
    // Number of tiles along the depth dimension. Must be a positive power-of-2
    // and less than or equal to Depth.
    // TODO(mgottscho): Relax this requirement to be any positive number <= Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width dimension. Must be a positive power-of-2
    // and less than or equal to Width.
    // TODO(mgottscho): Relax this requirement to be any positive number <= Depth.
    parameter int WidthTiles = 1,
    // Must be at least 1 and a positive-power-of-2 such that FaninPerStage ** Stages == DepthTiles
    // for some positive integer Stages.
    // High FaninPerStage results in lower latency but worse static timing.
    //
    // TODO(mgottscho): Relax this requirement so we can achieve design points with any desired
    // FaninPerStage and resulting number of stages with a ragged tree,
    // i.e., cases where FaninPerStage ** Stages > DepthTiles rather than FaninPerStage ** Stages == DepthTiles.
    parameter int FaninPerStage = DepthTiles,
    // If 1, then reset datapath flops. Otherwise, datapath flops are not reset.
    parameter bit EnableReset = 0,
    localparam int Stages = (FaninPerStage > 1) ? br_math::clogb(FaninPerStage, DepthTiles) : 1,
    localparam int TileWidth = br_math::ceil_div(Width, WidthTiles),
    localparam int Latency = Stages - 1
) (
    // Posedge-triggered clock.
    input  logic                                                 clk,
    // Synchronous active-high reset.
    input  logic                                                 rst,
    input  logic [DepthTiles-1:0][WidthTiles-1:0]                tile_valid,
    input  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_data,
    output logic                                                 valid,
    output logic [     Width-1:0]                                data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  // DepthTiles checks
  `BR_ASSERT_STATIC(depth_tiles_gte1_a, DepthTiles >= 1)
  `BR_ASSERT_STATIC(depth_tiles_power_of_2_a, br_math::is_power_of_2(DepthTiles))

  // WidthTiles checks
  `BR_ASSERT_STATIC(width_tiles_gte1_a, WidthTiles >= 1)
  `BR_ASSERT_STATIC(width_tiles_power_of_2_a, br_math::is_power_of_2(WidthTiles))

  // FaninPerStage checks
  `BR_ASSERT_STATIC(fanin_per_stage_gte_1_a, FaninPerStage >= 1)
  `BR_ASSERT_STATIC(fanin_per_stage_power_of_2_a, br_math::is_power_of_2(FaninPerStage))
  `BR_ASSERT_STATIC(fanin_per_stage_lte_depth_tiles_a, FaninPerStage <= DepthTiles)
  `BR_ASSERT_STATIC(derived_stages_gte1_a, Stages >= 1)
  `BR_ASSERT_STATIC(fanin_per_stage_pow_check_a, (FaninPerStage ** Stages) == DepthTiles)

`ifdef SV_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  logic [DepthTiles-1:0] depth_tile_valid;
  for (genvar d = 0; d < DepthTiles; d++) begin : gen_d
    assign depth_tile_valid[d] = |tile_valid[d];
    `BR_ASSERT_INTG(widthwise_tile_valid_lockstep_a, tile_valid[d] == '0 || tile_valid[d] == '1)
  end
  `BR_ASSERT_INTG(depthwise_tile_valid_onehot0_a, $onehot0(depth_tile_valid))
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // SV_ASSERT_ON

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // TODO(mgottscho): implement
  `BR_UNUSED_TODO(todo_tile_valid, tile_valid)
  `BR_UNUSED_TODO(todo_tile_data, tile_data)
  `BR_TIEOFF_ZERO_TODO(todo_valid, valid)
  `BR_TIEOFF_ZERO_TODO(todo_data, data)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(valid_propagation_a, |tile_valid |-> ##Stages valid)
  if (Stages > 0) begin : gen_stages_gt0
    `BR_ASSERT_IMPL(data_propagation_a, valid |-> $past(|tile_valid, Stages))
  end else begin : gen_stages_eq0
    `BR_ASSERT_IMPL(data_propagation_a, valid == |tile_valid)
  end

  // Rely on submodule implementation checks

endmodule : br_ram_data_rd_pipe
