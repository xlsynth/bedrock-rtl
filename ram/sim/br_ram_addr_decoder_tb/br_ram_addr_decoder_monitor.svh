// SPDX-License-Identifier: Apache-2.0

class br_ram_addr_decoder_monitor #(
    parameter int Tiles = 1,
    parameter int AddrWidth = 1,
    parameter int DataWidth = 1,
    parameter bit RecordTile = 1'b1
) extends br_dv_monitor #(
    .ItemType(br_ram_addr_decoder_item)
);
  local virtual br_dv_clk_rst_if clk_rst_vif;
  local longint unsigned next_id;
  local longint unsigned observed_cycle;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(AddrWidth)
  )
  addr_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(DataWidth)
  )
  data_vif;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(Tiles),
                   .Width(AddrWidth)
               ) addr_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(Tiles),
                   .Width(DataWidth)
               ) data_vif);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.addr_vif = addr_vif;
    this.data_vif = data_vif;
    next_id = 0;
    observed_cycle = 0;
    fork
      monitor();
    join_none
  endfunction

  task publish_observed_item(input int unsigned tile);
    br_ram_addr_decoder_item item;

    item = new(
        64'(data_vif.data[tile]),
        RecordTile,
        RecordTile ? tile : 0,
        next_id,
        $time,
        observed_cycle,
        64'(addr_vif.data[tile]),
        1'b1,
        bit'(data_vif.valid[tile])
    );
    publish(item);
    next_id++;
  endtask

  task monitor();
    forever begin
      @(posedge clk_rst_vif.clk);
      observed_cycle++;
      #1step;
      if (!clk_rst_vif.rst) begin
        for (int i = 0; i < Tiles; i++) begin
          if (addr_vif.valid[i]) begin
            publish_observed_item(i);
          end
        end
      end
    end
  endtask
endclass : br_ram_addr_decoder_monitor
