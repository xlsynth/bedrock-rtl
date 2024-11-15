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
// Decodes and steers an input address and data to one output tile based on the
// most-significant bits of the address.
//
// Works for any RAM depth >= 2 and any number of output tiles >= 1 that evenly
// divides the RAM depth. If RAM depth is a power-of-2 then the implementation is optimized.
//
// The latency is given by Stages. If Stages is 0, then the module is purely combinational;
// if 1, then there is a single pipeline register stage. Values greater than 1 work but don't
// pipeline the logic inside the decoding tree, they just retime the decoded outputs.

`include "br_asserts_internal.svh"

module br_ram_addr_decoder #(
    // Depth of the RAM. Must be at least 2.
    parameter int Depth = 2,
    // Sideband signals to pipeline in lockstep with the address decoding.
    // Safe to tie-off if not used. Must be at least 1.
    parameter int DataWidth = 1,
    // Number of output address tiles. Must be at least 1 and evenly divide Depth.
    parameter int Tiles = 1,
    // Pipeline depth. Must be at least 0.
    // Values greater than 1 are of dubious utility but don't hurt anything.
    parameter int Stages = 0,
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int InputAddressWidth = $clog2(Depth),
    localparam int OutputAddressWidth = $clog2(TileDepth)
) (
    // Posedge-triggered clock.
    // Can be unused if Stages == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 clk,
    // Synchronous active-high reset.
    // Can be unused if Stages == 0.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                                                 rst,
    // Input address and data.
    input  logic                                                 in_valid,
    input  logic [InputAddressWidth-1:0]                         in_addr,
    input  logic [        DataWidth-1:0]                         in_data,
    // Output tile addresses and data.
    output logic [            Tiles-1:0]                         out_valid,
    output logic [            Tiles-1:0][OutputAddressWidth-1:0] out_addr,
    output logic [            Tiles-1:0][         DataWidth-1:0] out_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte1_a, Depth >= 2)
  `BR_ASSERT_STATIC(data_width_gte1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(tiles_gte1_a, Tiles >= 1)
  `BR_ASSERT_STATIC(tiles_evenly_divides_depth_a, (Tiles * TileDepth) == Depth)
  `BR_ASSERT_STATIC(stages_gte0_a, Stages >= 0)

  `BR_ASSERT_INTG(in_addr_in_range_a, in_valid |-> in_addr < Depth)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Base case: single tile, i.e., just a simple delay register
  if (Tiles == 1) begin : gen_tiles_eq1
    `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth == InputAddressWidth)

    br_delay_valid #(
        .Width(OutputAddressWidth + DataWidth),
        .NumStages(Stages)
    ) br_delay_valid (
        .clk,
        .rst,
        .in_valid(in_valid),
        .in({in_addr, in_data}),
        .out_valid(out_valid),
        .out({out_addr, out_data}),
        .out_valid_stages(),  // unused
        .out_stages()  // unused
    );

    // Common case: multiple tiles, i.e., requires decoding to one of them (replicated delay registers)
  end else begin : gen_tiles_gt1
    `BR_ASSERT_STATIC(output_address_width_ok_a, OutputAddressWidth < InputAddressWidth)

    logic [Tiles-1:0]                         internal_out_valid;
    logic [Tiles-1:0][OutputAddressWidth-1:0] internal_out_addr;
    logic [Tiles-1:0][         DataWidth-1:0] internal_out_data;

    // If Depth is a power of 2 (and Tiles evenly divides it), then we know we can
    // decode the address by looking only at the MSBs as the tile select bits,
    // and simply slice them off.
    if (br_math::is_power_of_2(Depth)) begin : gen_demux_impl
      localparam int TileSelectWidth = $clog2(Tiles);
      localparam int SelectMsb = InputAddressWidth - 1;
      localparam int SelectLsb = (SelectMsb - TileSelectWidth) + 1;
      `BR_ASSERT_STATIC(select_check_a, SelectMsb >= SelectLsb)

      br_demux_bin #(
          .NumSymbolsOut(Tiles),
          .SymbolWidth  (OutputAddressWidth + DataWidth)
      ) br_demux_bin (
          .select(in_addr[SelectMsb:SelectLsb]),
          .in_valid(in_valid),
          .in({in_addr[OutputAddressWidth-1:0], in_data}),
          .out_valid(internal_out_valid),
          .out({internal_out_addr, internal_out_data})
      );

      // If Depth is not a power-of-2 we cannot just slice off the MSBs for the tile select.
      // We have to look at the address range and steer it with bit overlaps.
    end else begin : gen_compare_impl
      for (genvar i = 0; i < Tiles; i++) begin : gen_compare
        // inclusive
        localparam logic [InputAddressWidth-1:0] TileBaseAddress = TileDepth * i;
        // exclusive
        localparam logic [InputAddressWidth-1:0] TileBoundAddress = TileDepth * (i + 1);

        assign internal_out_valid[i] = in_valid &&
            // Lint waiver needed because when i == 0, this subexpression is always true.
            // ri lint_check_waive INVALID_COMPARE
            (in_addr >= TileBaseAddress) && (in_addr < TileBoundAddress);
        assign internal_out_addr[i] = in_addr[OutputAddressWidth-1:0];
        assign internal_out_data[i] = in_data;
      end
    end

    // Replicate to reduce register fanout when Stages >= 1
    for (genvar i = 0; i < Tiles; i++) begin : gen_out
      br_delay_valid #(
          .Width(OutputAddressWidth + DataWidth),
          .NumStages(Stages)
      ) br_delay_valid (
          .clk,
          .rst,
          .in_valid(internal_out_valid[i]),
          .in({internal_out_addr[i], internal_out_data[i]}),
          .out_valid(out_valid[i]),
          .out({out_addr[i], out_data[i]}),
          .out_valid_stages(),  // unused
          .out_stages()  // unused
      );
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(out_valid_onehot0_a, $onehot0(out_valid))
  for (genvar i = 0; i < Tiles; i++) begin : gen_out_addr_checks
    `BR_ASSERT_IMPL(out_addr_in_range_a, out_valid[i] |-> out_addr[i] < TileDepth)
  end

  if (Stages > 0) begin : gen_impl_checks_delayed
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |=> $onehot(out_valid))
    for (genvar i = 0; i < Tiles; i++) begin : gen_tiles_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> $past(
                          in_valid, Stages
                      ) && (out_addr[i] == $past(
                          in_addr[OutputAddressWidth-1:0], Stages
                      )))
    end
  end else begin : gen_impl_checks_not_delayed
    `BR_ASSERT_IMPL(valid_propagation_a, in_valid |-> $onehot(out_valid))
    for (genvar i = 0; i < Tiles; i++) begin : gen_tiles_check
      `BR_ASSERT_IMPL(out_addr_correct_a,
                      out_valid[i] |-> in_valid && (out_addr[i] == in_addr[OutputAddressWidth-1:0]))
    end
  end

endmodule : br_ram_addr_decoder
