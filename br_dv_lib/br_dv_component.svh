// SPDX-License-Identifier: Apache-2.0

class br_dv_component;
  protected br_dv_context ctx;

  function new(input br_dv_context ctx = null);
    this.ctx = ctx;
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvComponent;
  endfunction

  virtual function bit has_item();
    return 1'b0;
  endfunction
endclass
