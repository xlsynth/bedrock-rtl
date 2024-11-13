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
    // Must be at least 1, a positive-power-of-2, and at most Tiles.
    // High FanoutPerStage results in lower latency but worse static timing.
    parameter int FanoutPerStage = Tiles,
    localparam int Stages = (FanoutPerStage > 1) ? br_math::clogb(FanoutPerStage, Tiles) : 1,
    localparam int AddressWidth = $clog2(Depth),
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int TileAddressWidth = $clog2(TileDepth),
    localparam int Latency = Stages - 1
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

  // FanoutPerStage checks
  `BR_ASSERT_STATIC(fanout_per_stage_gte_1_a, FanoutPerStage >= 1)
  `BR_ASSERT_STATIC(fanout_per_stage_power_of_2_a, br_math::is_power_of_2(FanoutPerStage))
  `BR_ASSERT_STATIC(fanout_per_stage_lte_tiles_a, FanoutPerStage <= Tiles)

  `BR_ASSERT(addr_in_range_a, valid |-> addr < Depth)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Stages checks
  `BR_ASSERT_STATIC(stages_gte1_a, Stages >= 1)
  `BR_ASSERT_STATIC(stages_pow_check_a, (FanoutPerStage ** Stages) == Tiles)

  // Ineffective net waivers are because we make a big 2D array of Stages x Tiles but
  // we don't use all of the Tiles dimension until the last stage. It's not a very
  // nice array structure so it's a bit tricky to code this up with generate loops.

  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0] stage_in_valid;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0][AddressWidth-1:0] stage_in_addr;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0][DataWidth-1:0] stage_in_data;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0] stage_out_valid;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0][AddressWidth-1:0] stage_out_addr;
  // ri lint_check_waive INEFFECTIVE_NET
  logic [Stages-1:0][Tiles-1:0][DataWidth-1:0] stage_out_data;

  for (genvar s = 0; s < Stages; s++) begin : gen_stage
    localparam int InputLanes = FanoutPerStage ** s;
    localparam int OutputLanes = FanoutPerStage ** (s + 1);
    localparam int StageInputAddressWidth = AddressWidth - $clog2(InputLanes);
    localparam int StageOutputAddressWidth = AddressWidth - $clog2(OutputLanes);
    localparam int StageOutputAddressPadWidth = AddressWidth - StageOutputAddressWidth;

    `BR_ASSERT_STATIC(input_fanout_lte_tiles_a, InputLanes <= Tiles)
    `BR_ASSERT_STATIC(output_fanout_lte_tiles_a, OutputLanes <= Tiles)
    `BR_ASSERT_STATIC(stage_input_address_width_range_a,
                      (StageInputAddressWidth > 0) && (StageInputAddressWidth <= AddressWidth))
    `BR_ASSERT_STATIC(stage_output_address_width_range_a,
                      (StageOutputAddressWidth > 0) && (StageOutputAddressWidth <= AddressWidth))

    // Local stage inputs
    logic [InputLanes-1:0] local_stage_in_valid;
    logic [InputLanes-1:0][StageInputAddressWidth-1:0] local_stage_in_addr;
    logic [InputLanes-1:0][DataWidth-1:0] local_stage_in_data;

    // Local stage outputs
    logic [InputLanes-1:0][FanoutPerStage-1:0] local_stage_out_valid;
    logic [InputLanes-1:0][FanoutPerStage-1:0][StageOutputAddressWidth-1:0] local_stage_out_addr;
    logic [InputLanes-1:0][FanoutPerStage-1:0][DataWidth-1:0] local_stage_out_data;

    for (genvar il = 0; il < InputLanes; il++) begin : gen_stage_decoders
      // Full width inter-stage wiring
      if (s == 0) begin : gen_s_eq_0
        assign stage_in_valid[s][il] = valid;
        assign stage_in_addr[s][il]  = addr;
        assign stage_in_data[s][il]  = data;
      end else begin : gen_s_gt_0
        assign stage_in_valid[s][il] = stage_out_valid[s-1][il];
        assign stage_in_addr[s][il]  = stage_out_addr[s-1][il];
        assign stage_in_data[s][il]  = stage_out_data[s-1][il];
      end

      assign local_stage_in_valid[il] = stage_in_valid[s][il];
      // ri lint_check_waive FULL_RANGE
      assign local_stage_in_addr[il]  = stage_in_addr[s][il][StageInputAddressWidth-1:0];
      if (AddressWidth > StageInputAddressWidth) begin : gen_unused_in
        `BR_UNUSED_NAMED(stage_in_addr_msbs,
                         stage_in_addr[s][il][AddressWidth-1:StageInputAddressWidth])
      end
      assign local_stage_in_data[il] = stage_in_data[s][il];

      br_ram_addr_decoder_stage #(
          .InputAddressWidth(StageInputAddressWidth),
          .Fanout(FanoutPerStage),
          .RegisterOutputs(1)
      ) br_ram_addr_decoder_stage (
          .clk,
          .rst,
          .in_valid (local_stage_in_valid[il]),
          .in_addr  (local_stage_in_addr[il]),
          .in_data  (local_stage_in_data[il]),
          .out_valid(local_stage_out_valid[il]),
          .out_addr (local_stage_out_addr[il]),
          .out_data (local_stage_out_data[il])
      );

      for (genvar fo = 0; fo < FanoutPerStage; fo++) begin : gen_output_fanout
        localparam int OutputLane = (il * FanoutPerStage) + fo;

        assign stage_out_valid[s][OutputLane] = local_stage_out_valid[il][fo];
        assign stage_out_addr[s][OutputLane] = {
          // ri lint_check_waive ZERO_REP
          {StageOutputAddressPadWidth{1'b0}},
          local_stage_out_addr[il][fo]
        };
        assign stage_out_data[s][OutputLane] = local_stage_out_data[il][fo];
      end
    end

    // Earlier stages don't use all input lanes or drive all output lanes. Tie them off appropriately.
    for (genvar il = InputLanes; il < Tiles; il++) begin : gen_input_lane_tieoffs
      `BR_TIEOFF_ZERO_NAMED(stage_in_valid, stage_in_valid[s][il])
      `BR_TIEOFF_ZERO_NAMED(stage_in_addr, stage_in_addr[s][il])
      `BR_TIEOFF_ZERO_NAMED(stage_in_data, stage_in_data[s][il])
      `BR_UNUSED_NAMED(stage_in_valid, stage_in_valid[s][il])
      `BR_UNUSED_NAMED(stage_in_addr, stage_in_addr[s][il])
      `BR_UNUSED_NAMED(stage_in_data, stage_in_data[s][il])
    end

    for (genvar ol = OutputLanes; ol < Tiles; ol++) begin : gen_output_lane_tieoffs
      `BR_TIEOFF_ZERO_NAMED(stage_out_valid, stage_out_valid[s][ol])
      `BR_TIEOFF_ZERO_NAMED(stage_out_addr, stage_out_addr[s][ol])
      `BR_TIEOFF_ZERO_NAMED(stage_out_data, stage_out_data[s][ol])
      `BR_UNUSED_NAMED(stage_out_valid, stage_out_valid[s][ol])
      `BR_UNUSED_NAMED(stage_out_addr, stage_out_addr[s][ol])
      `BR_UNUSED_NAMED(stage_out_data, stage_out_data[s][ol])
    end
  end

  for (genvar t = 0; t < Tiles; t++) begin : gen_outputs
    // ri lint_check_waive FULL_RANGE
    assign tile_valid[t] = stage_out_valid[Stages-1][t];
    // ri lint_check_waive FULL_RANGE
    assign tile_addr[t]  = stage_out_addr[Stages-1][t][TileAddressWidth-1:0];
    assign tile_data[t]  = stage_out_data[Stages-1][t];
    if ((AddressWidth - 1) >= TileAddressWidth) begin : gen_unused
      `BR_UNUSED_NAMED(stage_out_addr_msbs,
                       stage_out_addr[Stages-1][t][AddressWidth-1:TileAddressWidth])
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(tile_valid_onehot0_a, $onehot0(tile_valid))
  `BR_ASSERT_IMPL(latency_a, valid |-> ##Latency $onehot(tile_valid))

  for (genvar t = 0; t < Tiles; t++) begin : gen_tile_checks
    `BR_ASSERT_IMPL(tile_addr_in_range_a, tile_valid[t] |-> tile_addr[t] < TileDepth)
    // Generate branch needed because we cannot use a zero delay in a $past expression.
    if (Latency > 0) begin : gen_latency_gt0
      `BR_ASSERT_IMPL(tile_valid_a, tile_valid[t] |-> $past(valid, Latency))
      `BR_ASSERT_IMPL(tile_addr_a,
                      tile_valid[t] |-> tile_addr[t] == $past(addr[TileAddressWidth-1:0], Latency))
      `BR_ASSERT_IMPL(tile_data_a, tile_valid[t] |-> tile_data[t] == $past(data, Latency))
    end else begin : gen_latency_eq0
      `BR_ASSERT_IMPL(tile_valid_a, |tile_valid == valid)
      `BR_ASSERT_IMPL(tile_addr_a, tile_valid[t] |-> tile_addr[t] == addr[TileAddressWidth-1:0])
      `BR_ASSERT_IMPL(tile_data_a, tile_valid[t] |-> tile_data[t] == data)
    end
  end

  // Rely on submodule implementation checks

endmodule : br_ram_addr_decoder
