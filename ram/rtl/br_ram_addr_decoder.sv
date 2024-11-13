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

// Bedrock-RTL Address Decoder
//
// TODO(mgottscho): description

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_tieoff.svh"
`include "br_unused.svh"

module br_ram_addr_decoder #(
    // Number of entries in the RAM. Must be at least 2.
    parameter int Depth = 2,
    // Sideband signals to pipeline in lockstep with the address decoding.
    // Safe to tie-off if not used. Must be at least 1.
    parameter int DataWidth = 1,
    // Number of tiles along the depth dimension. Must be a positive power-of-2
    // and less than or equal to Depth.
    parameter int Tiles = 1,
    // Number of pipeline register stages inserted along the address path.
    // Must be at least 0 and less than or equal to $clog2(Tiles).
    parameter int Stages = 0,
    localparam int AddressWidth = $clog2(Depth),
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int TileAddressWidth = $clog2(TileDepth)
) (
    // Posedge-triggered clock.
    input  logic                                          clk,
    // Synchronous active-high reset.
    input  logic                                          rst,
    input  logic                                          valid,
    input  logic [AddressWidth-1:0]                       addr,
    input  logic [   DataWidth-1:0]                       data,
    output logic [       Tiles-1:0]                       tile_valid,
    output logic [       Tiles-1:0][TileAddressWidth-1:0] tile_addr,
    output logic [       Tiles-1:0][       DataWidth-1:0] tile_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(data_width_gte_1_a, DataWidth >= 1)

  // Tiles checks
  `BR_ASSERT_STATIC(tiles_positive_power_of_2_a, (Tiles > 0) && br_math::is_power_of_2(Tiles))
  `BR_ASSERT_STATIC(tiles_lte_depth_a, Tiles <= Depth)

  // Stages checks
  `BR_ASSERT_STATIC(stages_gte0_a, Stages >= 0)
  `BR_ASSERT_STATIC(stages_lte_clog2_tiles_a, Stages <= $clog2(Tiles))

  `BR_ASSERT(addr_in_range_a, valid |-> addr < Depth)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int ForksPerStage = (Stages > 1) ? br_math::ceil_div($clog2(Tiles), Stages) : 1;
  `BR_ASSERT_STATIC(forks_per_stage_pos_power_of_2_a,
                    (ForksPerStage > 0) && br_math::is_power_of_2(ForksPerStage))

  // Ineffective net waivers are because we make a big 2D array of Stages x Tiles but
  // we don't use all of the Tiles dimension until the last stage. It's not a very
  // nice array structure so it's a bit tricky to code this up with generate loops.

  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0] stage_in_valid;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0][AddressWidth-1:0] stage_in_addr;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0][DataWidth-1:0] stage_in_data;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0] stage_out_valid;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0][AddressWidth-1:0] stage_out_addr;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages:0][Tiles-1:0][DataWidth-1:0] stage_out_data;

  for (genvar s = 0; s <= Stages; s++) begin : gen_stage
    localparam int InputForks = ForksPerStage ** s;
    localparam int StageInputAddressWidth = AddressWidth - $clog2(InputForks);
    `BR_ASSERT_STATIC(input_forks_lte_tiles_a, InputForks <= Tiles)
    `BR_ASSERT_STATIC(stage_input_address_width_range_a,
                      (StageInputAddressWidth > 0) && (StageInputAddressWidth <= AddressWidth))

    for (genvar f = 0; f < InputForks; f++) begin : gen_forks
      if (s == 0) begin : gen_s_eq_0
        assign stage_in_valid[s][f] = valid;
        assign stage_in_addr[s][f]  = addr;
        assign stage_in_data[s][f]  = data;
      end else begin : gen_s_gt_0
        assign stage_in_valid[s][f] = stage_out_valid[s-1][f];
        // ri lint_check_waive FULL_RANGE
        assign stage_in_addr[s][f]  = stage_out_addr[s-1][f][StageInputAddressWidth-1:0];
        assign stage_in_data[s][f]  = stage_out_data[s-1][f];

        if ((AddressWidth - 1) >= StageInputAddressWidth) begin : gen_unused
          `BR_UNUSED_NAMED(stage_out_addr,
                           stage_out_addr[s-1][f][AddressWidth-1:StageInputAddressWidth])
        end
      end

      br_ram_addr_decoder_stage #(
          .InputAddressWidth(StageInputAddressWidth),
          .Forks(ForksPerStage),
          .RegisterOutputs(1)
      ) br_ram_addr_decoder_stage (
          .clk,
          .rst,
          .in_valid (stage_in_valid[s][f]),
          .in_addr  (stage_in_addr[s][f]),
          .in_data  (stage_in_data[s][f]),
          .out_valid(stage_out_valid[s][f]),
          .out_addr (stage_out_addr[s][f]),
          .out_data (stage_out_data[s][f])
      );
    end

    // Earlier stages don't drive all forks. Tie off the unused forks.
    for (genvar f = InputForks; f < Tiles; f++) begin : gen_forks_tied_off
      `BR_TIEOFF_ZERO_NAMED(stage_in_valid, stage_in_valid[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_in_addr, stage_in_addr[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_in_data, stage_in_data[s][f])
      `BR_UNUSED_NAMED(stage_in_valid, stage_in_valid[s][f])
      `BR_UNUSED_NAMED(stage_in_addr, stage_in_addr[s][f])
      `BR_UNUSED_NAMED(stage_in_data, stage_in_data[s][f])

      `BR_TIEOFF_ZERO_NAMED(stage_out_valid, stage_out_valid[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_out_addr, stage_out_addr[s][f])
      `BR_TIEOFF_ZERO_NAMED(stage_out_data, stage_out_data[s][f])
      `BR_UNUSED_NAMED(stage_out_valid, stage_out_valid[s][f])
      `BR_UNUSED_NAMED(stage_out_addr, stage_out_addr[s][f])
      `BR_UNUSED_NAMED(stage_out_data, stage_out_data[s][f])
    end
  end

  for (genvar t = 0; t < Tiles; t++) begin : gen_outputs
    // ri lint_check_waive FULL_RANGE
    assign tile_valid[t] = stage_out_valid[Stages][t];
    // ri lint_check_waive FULL_RANGE
    assign tile_addr[t]  = stage_out_addr[Stages][t][TileAddressWidth-1:0];
    assign tile_data[t]  = stage_out_data[Stages][t];
    if ((AddressWidth - 1) >= TileAddressWidth) begin : gen_unused
      `BR_UNUSED_NAMED(stage_out_addr_msbs,
                       stage_out_addr[Stages][t][AddressWidth-1:TileAddressWidth])
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(tile_valid_onehot0_a, $onehot0(tile_valid))
  `BR_ASSERT_IMPL(latency_a, valid |-> ##Stages $onehot(tile_valid))

  for (genvar t = 0; t < Tiles; t++) begin : gen_tile_checks
    `BR_ASSERT_IMPL(tile_addr_in_range_a, tile_valid[t] |-> tile_addr[t] < TileDepth)
    // Generate branch needed because we cannot use a zero delay in a $past expression.
    if (Stages > 0) begin : gen_stages_gt0
      `BR_ASSERT_IMPL(tile_valid_a, tile_valid[t] |-> $past(valid, Stages))
      `BR_ASSERT_IMPL(tile_addr_a,
                      tile_valid[t] |-> tile_addr[t] == $past(addr[TileAddressWidth-1:0], Stages))
      `BR_ASSERT_IMPL(tile_data_a, tile_valid[t] |-> tile_data[t] == $past(data, Stages))
    end else begin : gen_stages_eq0
      `BR_ASSERT_IMPL(tile_valid_a, |tile_valid == valid)
      `BR_ASSERT_IMPL(tile_addr_a, tile_valid[t] |-> tile_addr[t] == addr[TileAddressWidth-1:0])
      `BR_ASSERT_IMPL(tile_data_a, tile_valid[t] |-> tile_data[t] == data)
    end
  end

  // Rely on submodule implementation checks

endmodule : br_ram_addr_decoder
