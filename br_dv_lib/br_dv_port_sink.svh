// SPDX-License-Identifier: Apache-2.0

class br_dv_port_sink #(
    type ItemType = br_item,
    type PortType = int
) extends br_dv_item_sink #(
    .ItemType(ItemType)
);
  typedef br_dv_port_sink_target#(
      .ItemType(ItemType),
      .PortType(PortType)
  ) TargetType;

  local TargetType target;
  local PortType   port;

  function new(input TargetType target, input PortType port);
    this.target = target;
    this.port   = port;
  endfunction

  virtual task write(input ItemType item);
    target.write_port(port, item);
  endtask
endclass : br_dv_port_sink
