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

module br_ram_rd_data_pipe #(
    // Number of entries in the RAM. Must be at least 2.
    parameter int Depth = 2,
    // Must be at least 1.
    parameter int DataWidth = 1,
    // Number of tiles along the depth dimension. Must be a positive power-of-2
    // and less than or equal to Depth.
    parameter int Tiles = 1,
    // Number of pipeline register stages inserted along the datapath.
    // Must be at least 0 and less than or equal to $clog2(Tiles).
    parameter int Stages = 0
) (
    // Posedge-triggered clock.
    input  logic                                clk,
    // Synchronous active-high reset.
    input  logic                                rst,
    input  logic [    Tiles-1:0]                tile_valid,
    input  logic [    Tiles-1:0][DataWidth-1:0] tile_data,
    output logic                                valid,
    output logic [DataWidth-1:0]                data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(data_width_gte_1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(tiles_gte0_a, Tiles > 0)
  `BR_ASSERT_STATIC(tiles_power_of_2_a, br_math::is_power_of_2(Tiles))
  `BR_ASSERT_STATIC(stages_gte0_a, Stages >= 0)
  `BR_ASSERT_STATIC(stages_lte_tiles_a, Stages <= $clog2(Tiles))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // TODO(mgottscho): implement
  `BR_TIEOFF_ZERO_TODO(todo_valid, valid)
  `BR_TIEOFF_ZERO_TODO(todo_data, data)
  `BR_UNUSED_TODO(todo_tile_valid, tile_valid)
  `BR_UNUSED_TODO(todo_tile_data, tile_data)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // TODO(mgottscho): implement

  // Rely on submodule implementation checks

endmodule : br_ram_rd_data_pipe
