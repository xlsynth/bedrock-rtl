// SPDX-License-Identifier: Apache-2.0

class br_dv_env extends br_dv_agent;
  function new(input br_dv_context ctx = null);
    super.new(ctx);
  endfunction

  virtual function void build();
  endfunction

  virtual function void connect();
  endfunction
endclass : br_dv_env
