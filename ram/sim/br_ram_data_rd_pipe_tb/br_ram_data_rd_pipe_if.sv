// SPDX-License-Identifier: Apache-2.0

interface br_ram_data_rd_pipe_input_if #(
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1,
    localparam int TileWidth = br_math::ceil_div(Width, WidthTiles)
);
  logic [DepthTiles-1:0][WidthTiles-1:0]                tile_valid;
  logic [DepthTiles-1:0][WidthTiles-1:0][TileWidth-1:0] tile_data;
endinterface : br_ram_data_rd_pipe_input_if

interface br_ram_data_rd_pipe_output_if #(
    parameter int Width = 1
);
  logic             valid;
  logic [Width-1:0] data;
endinterface : br_ram_data_rd_pipe_output_if
