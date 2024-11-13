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
`include "br_tieoff.svh"
`include "br_unused.svh"

module br_ram_addr_decoder #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    // Number of tiles along the depth dimension. Must be a positive power-of-2
    // and less than or equal to Depth.
    parameter int Tiles = 1,
    // Number of pipeline register stages inserted along the address path.
    // Must be a positive power-of-2 that is less than or equal to Tiles.
    parameter int Stages = 0,
    localparam int AddressWidth = $clog2(Depth),
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int TileAddressWidth = $clog2(TileDepth)
) (
    // Posedge-triggered clock.
    input  logic                                          clk,
    // Synchronous active-high reset.
    input  logic                                          rst,
    input  logic                                          addr_valid,
    input  logic [AddressWidth-1:0]                       addr,
    output logic [       Tiles-1:0]                       tile_addr_valid,
    output logic [       Tiles-1:0][TileAddressWidth-1:0] tile_addr
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)

  // Tiles checks
  `BR_ASSERT_STATIC(tiles_positive_power_of_2_a, (Tiles > 0) && br_math::is_power_of_2(Tiles))
  `BR_ASSERT_STATIC(tiles_lte_depth_a, Tiles <= Depth)

  // Stages checks
  `BR_ASSERT_STATIC(stages_gte0_a, Stages >= 0)
  `BR_ASSERT_STATIC(stages_positive_power_of_2_a, br_math::is_power_of_2(Stages))
  `BR_ASSERT_STATIC(stages_lte_clog2_tiles_a, Stages <= $clog2(Tiles))

  // TODO(mgottscho): write more

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int ForksPerStage = (Stages > 1) ? br_math::ceil_div($clog2(Tiles), Stages) : 1;
  `BR_ASSERT_STATIC(forks_per_stage_pos_power_of_2_a,
                    (ForksPerStage > 0) && br_math::is_power_of_2(ForksPerStage))

  logic [Stages:0][Tiles-1:0] stage_in_addr_valid;
  logic [Stages:0][Tiles-1:0][AddressWidth-1:0] stage_in_addr;
  logic [Stages:0][Tiles-1:0] stage_out_addr_valid;
  logic [Stages:0][Tiles-1:0][AddressWidth-1:0] stage_out_addr;

  for (genvar s = 0; s <= Stages; s++) begin : gen_stage
    localparam int InputForks = ForksPerStage ** s;
    localparam int StageInputAddressWidth = AddressWidth - $clog2(InputForks);
    `BR_ASSERT_STATIC(input_forks_lte_tiles_a, InputForks <= Tiles)
    `BR_ASSERT_STATIC(stage_input_address_width_range_a,
                      (StageInputAddressWidth > 0) && (StageInputAddressWidth <= AddressWidth))

    for (genvar f = 0; f < InputForks; f++) begin : gen_forks
      if (s == 0) begin : gen_s_eq_0
        assign stage_in_addr_valid[0][f] = addr_valid;
        assign stage_in_addr[0][f] = addr;

      end else begin : gen_s_gt_0
        assign stage_in_addr_valid[s][f] = stage_out_addr_valid[s-1][f];
        assign stage_in_addr[s][f] = stage_out_addr[s-1][f][StageInputAddressWidth-1:0];

        `BR_UNUSED_NAMED(stage_out_addr,
                         stage_out_addr[s-1][f][AddressWidth-1:StageInputAddressWidth])
      end

      br_ram_addr_decoder_stage #(
          .InputAddressWidth(StageInputAddressWidth),
          .Forks(ForksPerStage),
          // TODO(mgottscho): make this a parameter
          .RegisterOutputs(1)
      ) br_ram_addr_decoder_stage (
          .clk,
          .rst,
          .in_addr_valid(stage_in_addr_valid[s][f]),
          .in_addr(stage_in_addr[s][f]),
          .out_addr_valid(stage_out_addr_valid[s][f]),
          .out_addr(stage_out_addr[s][f])
      );
    end

    // Earlier stages don't drive all forks. Tie off the unused forks.
    for (genvar f = InputForks; f < Tiles; f++) begin : gen_forks_tied_off
      `BR_UNUSED_NAMED(stage_in_addr_valid, stage_in_addr_valid[s][f])
      `BR_UNUSED_NAMED(stage_in_addr, stage_in_addr[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_out_addr_valid, stage_out_addr_valid[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_out_addr, stage_out_addr[s][f])
    end
  end

  for (genvar t = 0; t < Tiles; t++) begin : gen_outputs
    // ri lint_check_waive FULL_RANGE
    assign tile_addr_valid[t] = stage_out_addr_valid[Stages][t];
    // ri lint_check_waive FULL_RANGE
    assign tile_addr[t] = stage_out_addr[Stages][t][TileAddressWidth-1:0];
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // TODO(mgottscho): Write more
  // Rely on submodule implementation checks

endmodule : br_ram_addr_decoder
