// SPDX-License-Identifier: Apache-2.0

class br_dv_sequence_base extends br_dv_component;
  protected bit started;

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    started = 1'b0;
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvSequence;
  endfunction

  function bit is_started();
    return started;
  endfunction

  virtual function bit is_running();
    return is_started() || has_item();
  endfunction

  virtual task start();
    $fatal(1, "sequence start is not implemented");
  endtask
endclass
