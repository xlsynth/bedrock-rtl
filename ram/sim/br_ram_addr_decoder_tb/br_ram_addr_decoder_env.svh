// SPDX-License-Identifier: Apache-2.0

class br_ram_addr_decoder_env #(
    parameter int InputAddressWidth = 1,
    parameter int DataWidth = 1,
    parameter int Tiles = 1,
    parameter int OutputAddressWidth = 1,
    parameter longint unsigned MaxAddressValue = 64'hffff_ffff_ffff_ffff
) extends br_dv_env;
  local int tile_depth;
  local int stages;

  local virtual br_dv_clk_rst_if clk_rst_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(InputAddressWidth)
  )
  in_addr_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(DataWidth)
  )
  in_data_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(OutputAddressWidth)
  )
  out_addr_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(DataWidth)
  )
  out_data_vif;

  br_dv_clk_rst_driver clk_rst_driver;
  br_ram_addr_decoder_driver #(
      .AddrWidth(InputAddressWidth),
      .DataWidth(DataWidth)
  ) input_driver;
  br_ram_addr_decoder_random_sequence #(.MaxAddressValue(MaxAddressValue)) input_sequence;
  br_ram_addr_decoder_monitor #(
      .Tiles(1),
      .AddrWidth(InputAddressWidth),
      .DataWidth(DataWidth),
      .RecordTile(0)
  ) input_monitor;
  br_ram_addr_decoder_monitor #(
      .Tiles(Tiles),
      .AddrWidth(OutputAddressWidth),
      .DataWidth(DataWidth),
      .RecordTile(1)
  ) output_monitor;
  br_ram_addr_decoder_scoreboard scoreboard;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(1),
                   .Width(InputAddressWidth)
               ) in_addr_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(1),
                   .Width(DataWidth)
               ) in_data_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(Tiles),
                   .Width(OutputAddressWidth)
               ) out_addr_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(Tiles),
                   .Width(DataWidth)
               ) out_data_vif,
               input int tile_depth, input int stages);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.in_addr_vif = in_addr_vif;
    this.in_data_vif = in_data_vif;
    this.out_addr_vif = out_addr_vif;
    this.out_data_vif = out_data_vif;
    this.tile_depth = tile_depth;
    this.stages = stages;
    build();
    connect();
  endfunction

  virtual function void build();
    clk_rst_driver = new(ctx, clk_rst_vif);
    input_driver = new(ctx, clk_rst_vif, in_addr_vif, in_data_vif);
    input_sequence = new(ctx);
    input_monitor = new(ctx, clk_rst_vif, in_addr_vif, in_data_vif);
    output_monitor = new(ctx, clk_rst_vif, out_addr_vif, out_data_vif);
    scoreboard = new(ctx, tile_depth, stages);
  endfunction

  virtual function void connect();
    input_sequence.connect(input_driver);
    input_monitor.connect_sink(scoreboard.get_sink(BrRamAddrDecoderIn));
    output_monitor.connect_sink(scoreboard.get_sink(BrRamAddrDecoderOut));
  endfunction
endclass : br_ram_addr_decoder_env
