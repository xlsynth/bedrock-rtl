// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_ram_invariant #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit WolperColorEn = 0,
    parameter bit EnableBypass = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int FlopRamDepthTiles = 1,
    parameter int FlopRamWidthTiles = 1,
    parameter int FlopRamAddressDepthStages = 0,
    parameter int FlopRamReadDataDepthStages = 0,
    parameter int FlopRamReadDataWidthStages = 0
) (
    input logic clk,
    input logic rst,
    input logic [$clog2(Width)-1:0] magic_bit
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;
  localparam int RamDepth = br_math::align_up(
      (EnableBypass && ((RamReadLatency > 0) || RegisterPopOutputs)) ? br_math::max2(
          1, Depth - RamReadLatency - 1
      ) : Depth,
      FlopRamDepthTiles
  );
  localparam int TileDepth = br_math::ceil_div(RamDepth, FlopRamDepthTiles);
  localparam int TileWidth = br_math::ceil_div(Width, FlopRamWidthTiles);
  localparam int MagicTileWidth = (FlopRamWidthTiles > 1) ? $clog2(FlopRamWidthTiles) : 1;
  localparam int MagicTileBitWidth = (TileWidth > 1) ? $clog2(TileWidth) : 1;

  logic [MagicTileWidth-1:0] magic_tile;
  logic [MagicTileBitWidth-1:0] magic_tile_bit;

  if (FlopRamWidthTiles > 1) begin : gen_magic_tile
    assign magic_tile = magic_bit / TileWidth;
  end else begin : gen_magic_tile_zero
    assign magic_tile = '0;
  end

  if (TileWidth > 1) begin : gen_magic_tile_bit
    assign magic_tile_bit = magic_bit % TileWidth;
  end else begin : gen_magic_tile_bit_zero
    assign magic_tile_bit = '0;
  end

  logic [Depth-1:0] fifo_magic_col;
  logic [RamDepth-1:0] fifo_tile_bits[FlopRamWidthTiles][TileWidth];

  for (genvar r = 0; r < FlopRamDepthTiles; r++) begin : gen_row
    for (genvar d = 0; d < TileDepth; d++) begin : gen_depth
      localparam int DepthIndex = (r * TileDepth) + d;
      if (DepthIndex < RamDepth) begin : gen_depth_in_range
        for (genvar c = 0; c < FlopRamWidthTiles; c++) begin : gen_col
          for (genvar b = 0; b < TileWidth; b++) begin : gen_bit
            assign fifo_tile_bits[c][b][DepthIndex] =
                br_ram_flops.gen_row[r].gen_col[c].br_ram_flops_tile.mem[d][0][b];
          end
        end
      end
    end
  end

  for (genvar i = 0; i < Depth; i++) begin : gen_magic_col_depth
    if (i < RamDepth) begin : gen_magic_col_in_range
      assign fifo_magic_col[i] = fifo_tile_bits[magic_tile][magic_tile_bit][i];
    end else begin : gen_magic_col_out_of_range
      assign fifo_magic_col[i] = 1'b0;
    end
  end

  `BR_ASSERT(fv_invariant_at_most_two_ones_a, $countones(fifo_magic_col) <= 2)

endmodule
