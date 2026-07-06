// SPDX-License-Identifier: Apache-2.0

class br_ram_data_rd_pipe_env #(
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1
) extends br_dv_env;
  local int expected_latency_cycles;
  local virtual br_dv_clk_rst_if clk_rst_vif;
  local virtual
  br_ram_data_rd_pipe_input_if #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  )
  in_vif;
  local virtual br_ram_data_rd_pipe_output_if #(.Width(Width)) out_vif;

  br_dv_clk_rst_driver clk_rst_driver;
  br_ram_data_rd_pipe_driver #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) input_driver;
  br_ram_data_rd_pipe_random_sequence #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) input_sequence;
  br_ram_data_rd_pipe_monitor #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) input_monitor;
  br_ram_data_rd_pipe_monitor #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) output_monitor;
  br_ram_data_rd_pipe_scoreboard scoreboard;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input virtual br_ram_data_rd_pipe_input_if #(
                   .Width(Width),
                   .DepthTiles(DepthTiles),
                   .WidthTiles(WidthTiles)
               ) in_vif,
               input virtual br_ram_data_rd_pipe_output_if #(.Width(Width)) out_vif,
               input int expected_latency_cycles);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.in_vif = in_vif;
    this.out_vif = out_vif;
    this.expected_latency_cycles = expected_latency_cycles;
    build();
    connect();
  endfunction

  virtual function void build();
    clk_rst_driver = new(ctx, clk_rst_vif);
    input_driver = new(ctx, clk_rst_vif, in_vif);
    input_sequence = new(ctx);
    input_monitor = new(ctx, clk_rst_vif, BrRamDataRdPipeMonitorInput, in_vif, null);
    output_monitor =
        new(ctx, clk_rst_vif, BrRamDataRdPipeMonitorOutput, null, out_vif, expected_latency_cycles);
    scoreboard = new(ctx, expected_latency_cycles);
  endfunction

  virtual function void connect();
    input_sequence.connect(input_driver);
    input_monitor.connect_sink(scoreboard.get_sink(BrRamDataRdPipeIn));
    output_monitor.connect_sink(scoreboard.get_sink(BrRamDataRdPipeOut));
  endfunction
endclass : br_ram_data_rd_pipe_env
