// SPDX-License-Identifier: Apache-2.0

class br_dv_agent extends br_dv_component;
  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvAgent;
  endfunction
endclass
