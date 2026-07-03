// SPDX-License-Identifier: Apache-2.0

virtual class br_dv_port_sink_target #(
    type ItemType = br_item,
    type PortType = int
) extends br_dv_component;
  function new(input br_dv_context ctx = null);
    super.new(ctx);
  endfunction

  pure virtual task write_port(input PortType port, input ItemType item);
endclass : br_dv_port_sink_target
