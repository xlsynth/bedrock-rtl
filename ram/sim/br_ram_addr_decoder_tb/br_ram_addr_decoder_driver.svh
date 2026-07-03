// SPDX-License-Identifier: Apache-2.0

class br_ram_addr_decoder_driver #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 1
) extends br_dv_driver #(
    .ItemType(br_ram_addr_decoder_item)
);
  local virtual br_dv_clk_rst_if clk_rst_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(AddrWidth)
  )
  addr_vif;
  local virtual
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(DataWidth)
  )
  data_vif;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if clk_rst_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(1),
                   .Width(AddrWidth)
               ) addr_vif,
               input virtual br_ram_addr_decoder_if #(
                   .Tiles(1),
                   .Width(DataWidth)
               ) data_vif);
    super.new(ctx);
    this.clk_rst_vif = clk_rst_vif;
    this.addr_vif = addr_vif;
    this.data_vif = data_vif;
    drive_idle();
  endfunction

  function void drive_idle();
    addr_vif.valid <= '0;
    addr_vif.data  <= '0;
    data_vif.valid <= '0;
    data_vif.data  <= '0;
  endfunction

  virtual task drive_item(input br_ram_addr_decoder_item item);
    if (item == null) begin
      @(posedge clk_rst_vif.clk);
      drive_idle();
      return;
    end

    @(posedge clk_rst_vif.clk);
    // DUT inputs are scalar streams modeled as one-lane interfaces in this TB.
    addr_vif.valid[0] <= item.has_addr;
    addr_vif.data[0]  <= AddrWidth'(item.addr);
    data_vif.valid[0] <= item.has_addr && item.has_data;
    data_vif.data[0]  <= DataWidth'(item.data);
  endtask
endclass : br_ram_addr_decoder_driver
