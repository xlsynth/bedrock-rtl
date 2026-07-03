// SPDX-License-Identifier: Apache-2.0

class br_dv_monitor #(
    type ItemType = br_item
) extends br_dv_component;
  local br_dv_item_sink #(.ItemType(ItemType)) sinks[$];

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvMonitor;
  endfunction

  function void connect_sink(input br_dv_item_sink#(.ItemType(ItemType)) sink);
    sinks.push_back(sink);
  endfunction

  task publish(input ItemType item);
    foreach (sinks[i]) begin
      sinks[i].write(item);
    end
  endtask

endclass
