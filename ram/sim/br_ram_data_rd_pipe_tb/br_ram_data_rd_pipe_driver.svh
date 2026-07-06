// SPDX-License-Identifier: Apache-2.0

class br_ram_data_rd_pipe_driver #(
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1
) extends br_dv_driver #(
    .ItemType(br_ram_data_rd_pipe_item)
);
  localparam int TileWidth = (Width + WidthTiles - 1) / WidthTiles;

  local virtual br_dv_clk_rst_if clk_rst_vif;
  local virtual
  br_ram_data_rd_pipe_input_if #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  )
  in_vif;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input virtual br_ram_data_rd_pipe_input_if #(
                   .Width(Width),
                   .DepthTiles(DepthTiles),
                   .WidthTiles(WidthTiles)
               ) in_vif);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.in_vif = in_vif;
    drive_idle();
  endfunction

  function void drive_idle();
    in_vif.tile_valid <= '0;
    in_vif.tile_data  <= '0;
  endfunction

  virtual task drive_item(input br_ram_data_rd_pipe_item item);
    if (item == null) begin
      @(posedge clk_rst_vif.clk);
      drive_idle();
      return;
    end

    @(posedge clk_rst_vif.clk);
    in_vif.tile_valid <= '0;
    in_vif.tile_data  <= '0;
    ctx.check(item.get_width() == Width, $sformatf(
              "br_ram_data_rd_pipe item width mismatch: exp=%0d act=%0d", Width, item.get_width()));
    ctx.check(item.depth_tile < DepthTiles, $sformatf(
              "br_ram_data_rd_pipe item depth tile out of range: depth_tile=%0d depth_tiles=%0d",
              item.depth_tile,
              DepthTiles
              ));
    if ((item.get_width() != Width) || (item.depth_tile >= DepthTiles)) return;

    if (item.valid) begin
      in_vif.tile_valid[item.depth_tile] <= '1;
    end
    for (int w = 0; w < WidthTiles; w++) begin
      for (int b = 0; b < TileWidth; b++) begin
        if (((w * TileWidth) + b) < Width) begin
          in_vif.tile_data[item.depth_tile][w][b] <= item.word_data[(w*TileWidth)+b];
        end
      end
    end
  endtask
endclass : br_ram_data_rd_pipe_driver
