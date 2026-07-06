// SPDX-License-Identifier: Apache-2.0

typedef enum {
  BrRamDataRdPipeMonitorInput,
  BrRamDataRdPipeMonitorOutput
} br_ram_data_rd_pipe_monitor_mode_e;

class br_ram_data_rd_pipe_monitor #(
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1
) extends br_dv_monitor #(
    .ItemType(br_ram_data_rd_pipe_item)
);
  localparam int TileWidth = (Width + WidthTiles - 1) / WidthTiles;

  local virtual br_dv_clk_rst_if clk_rst_vif;
  local br_ram_data_rd_pipe_monitor_mode_e mode;
  local int latency_cycles;
  local longint unsigned next_id;
  local longint unsigned observed_cycle;
  local virtual
  br_ram_data_rd_pipe_input_if #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  )
  in_vif;
  local virtual br_ram_data_rd_pipe_output_if #(.Width(Width)) out_vif;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input br_ram_data_rd_pipe_monitor_mode_e mode,
               input virtual br_ram_data_rd_pipe_input_if #(
                   .Width(Width),
                   .DepthTiles(DepthTiles),
                   .WidthTiles(WidthTiles)
               ) in_vif = null,
               input virtual br_ram_data_rd_pipe_output_if #(.Width(Width)) out_vif = null,
               input int latency_cycles = 0);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.mode = mode;
    this.in_vif = in_vif;
    this.out_vif = out_vif;
    this.latency_cycles = latency_cycles;
    next_id = 0;
    observed_cycle = 0;
    fork
      monitor();
    join_none
  endfunction

  task monitor();
    fork
      monitor_items();
      monitor_reset_cleared_output();
    join
  endtask

  task monitor_items();
    forever begin
      @(posedge clk_rst_vif.clk);
      observed_cycle++;
      if (clk_rst_vif.rst) begin
        next_id = 0;
      end else begin
        case (mode)
          BrRamDataRdPipeMonitorInput: publish_input_item();
          BrRamDataRdPipeMonitorOutput: publish_output_item();
          default: ctx.check(1'b0, "unknown br_ram_data_rd_pipe monitor mode");
        endcase
      end
    end
  endtask

  function longint unsigned get_observed_cycle();
    return observed_cycle;
  endfunction

  task monitor_reset_cleared_output();
    bit rst_prev_cycle = 1'b0;

    forever begin
      @(posedge clk_rst_vif.clk);
      // Synchronous reset is visible one cycle later; zero-latency configs are combinational.
      if (rst_prev_cycle && (mode == BrRamDataRdPipeMonitorOutput) && (latency_cycles > 0)) begin
        ctx.check(!out_vif.valid, "br_ram_data_rd_pipe output valid remained asserted after reset");
      end
      rst_prev_cycle = clk_rst_vif.rst;
    end
  endtask

  task publish_input_item();
    br_ram_data_rd_pipe_item item;

    for (int d = 0; d < DepthTiles; d++) begin
      if (|in_vif.tile_valid[d]) begin
        item = new(Width, 1'b1, d, next_id, observed_cycle, $time);
        for (int w = 0; w < WidthTiles; w++) begin
          for (int b = 0; b < TileWidth; b++) begin
            if (((w * TileWidth) + b) < Width) begin
              item.word_data[(w*TileWidth)+b] = in_vif.tile_data[d][w][b];
            end
          end
        end
        publish(item);
        next_id++;
      end
    end
  endtask

  task publish_output_item();
    br_ram_data_rd_pipe_item item;

    if (out_vif.valid) begin
      item = new(Width, 1'b1, 0, next_id, observed_cycle, $time);
      for (int b = 0; b < Width; b++) begin
        item.word_data[b] = out_vif.data[b];
      end
      publish(item);
      next_id++;
    end
  endtask
endclass : br_ram_data_rd_pipe_monitor
