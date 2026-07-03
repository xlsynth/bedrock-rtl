// SPDX-License-Identifier: Apache-2.0

class br_dv_clk_rst_driver extends br_dv_component;
  local virtual br_dv_clk_rst_if vif;

  function new(input br_dv_context ctx, input virtual br_dv_clk_rst_if vif);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
    this.vif = vif;
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvDriver;
  endfunction

  task wait_cycles(input int cycles = 1);
    repeat (cycles) @(posedge vif.clk);
  endtask

  task reset_dut(input int reset_cycles = 1);
    $display("Resetting DUT");
    wait_cycles();
    vif.rst = 1'b1;
    wait_cycles(reset_cycles);
    vif.rst = 1'b0;
  endtask
endclass
