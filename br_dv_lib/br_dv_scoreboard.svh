// SPDX-License-Identifier: Apache-2.0

class br_dv_scoreboard #(
    type ItemType = br_item
) extends br_dv_port_sink_target #(
    .ItemType(ItemType),
    .PortType(int)
);
  typedef br_dv_port_sink#(
      .ItemType(ItemType),
      .PortType(int)
  ) SinkType;

  localparam int ExpPort = 0;
  localparam int ActPort = 1;

  local ItemType exp_item_q[$];
  local ItemType act_item_q[$];
  local SinkType exp_sink;
  local SinkType act_sink;

  function new(input br_dv_context ctx = null);
    super.new(ctx);
    if (ctx != null) begin
      ctx.register(this);
    end
    exp_sink = new(this, ExpPort);
    act_sink = new(this, ActPort);
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvScoreboard;
  endfunction

  function br_dv_item_sink#(.ItemType(ItemType)) get_exp_sink();
    return exp_sink;
  endfunction

  function br_dv_item_sink#(.ItemType(ItemType)) get_act_sink();
    return act_sink;
  endfunction

  task write_port(input int port, input ItemType item);
    case (port)
      ExpPort: write_exp(item);
      ActPort: write_act(item);
      default: ctx.check(1'b0, $sformatf("unknown scoreboard write port %0d", port));
    endcase
  endtask

  task write_exp(input ItemType item);
    exp_item_q.push_back(item);
  endtask

  task write_act(input ItemType item);
    act_item_q.push_back(item);
  endtask

  function int unsigned get_pending_exp_items();
    return exp_item_q.size();
  endfunction

  function int unsigned get_pending_act_items();
    return act_item_q.size();
  endfunction

  task check_empty();
    ctx.check(exp_item_q.size() == 0, $sformatf(
              "scoreboard has %0d unmatched expected items", exp_item_q.size()));
    ctx.check(act_item_q.size() == 0, $sformatf(
              "scoreboard has %0d unmatched actual items", act_item_q.size()));
  endtask

  task check_all();
    compare_all();
    check_empty();
  endtask

  task compare_all();
    ItemType exp_item;
    ItemType act_item;

    while ((exp_item_q.size() != 0) && (act_item_q.size() != 0)) begin
      exp_item = exp_item_q.pop_front();
      act_item = act_item_q.pop_front();
      compare_item(exp_item, act_item);
    end
  endtask

  virtual task compare_item(input ItemType exp_item, input ItemType act_item);
    $fatal(1, "scoreboard compare_item is not implemented");
  endtask
endclass : br_dv_scoreboard
