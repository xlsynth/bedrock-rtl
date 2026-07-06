// SPDX-License-Identifier: Apache-2.0

typedef enum {
  BrRamDataRdPipeIn,
  BrRamDataRdPipeOut
} br_ram_data_rd_pipe_scoreboard_port_e;

class br_ram_data_rd_pipe_scoreboard extends br_dv_port_sink_target #(
    .ItemType(br_ram_data_rd_pipe_item),
    .PortType(br_ram_data_rd_pipe_scoreboard_port_e)
);
  typedef br_dv_port_sink#(
      .ItemType(br_ram_data_rd_pipe_item),
      .PortType(br_ram_data_rd_pipe_scoreboard_port_e)
  ) BrRamDataRdPipeSink;
  typedef br_dv_port_sink_target#(
      .ItemType(br_ram_data_rd_pipe_item),
      .PortType(br_ram_data_rd_pipe_scoreboard_port_e)
  ) BrRamDataRdPipeTarget;

  localparam string ScoreboardName = "br_ram_data_rd_pipe";

  local int expected_latency_cycles;
  local br_ram_data_rd_pipe_item exp_q[$];
  local br_ram_data_rd_pipe_item act_q[$];
  local BrRamDataRdPipeSink in_sink;
  local BrRamDataRdPipeSink out_sink;

  function new(input br_dv_context ctx = null, input int expected_latency_cycles = 0);
    super.new(ctx);
    this.expected_latency_cycles = expected_latency_cycles;
    if (ctx != null) begin
      ctx.register(this);
    end
    in_sink  = new(BrRamDataRdPipeTarget'(this), BrRamDataRdPipeIn);
    out_sink = new(BrRamDataRdPipeTarget'(this), BrRamDataRdPipeOut);
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvScoreboard;
  endfunction

  function BrRamDataRdPipeSink get_sink(input br_ram_data_rd_pipe_scoreboard_port_e port);
    case (port)
      BrRamDataRdPipeIn: return in_sink;
      BrRamDataRdPipeOut: return out_sink;
      default: return null;
    endcase
  endfunction

  task write_port(input br_ram_data_rd_pipe_scoreboard_port_e port,
                  input br_ram_data_rd_pipe_item item);
    case (port)
      BrRamDataRdPipeIn: write_in(item);
      BrRamDataRdPipeOut: write_out(item);
      default: ctx.check(1'b0, $sformatf("%s unknown write port %0d", ScoreboardName, port));
    endcase
  endtask

  task write_in(input br_ram_data_rd_pipe_item item);
    exp_q.push_back(predict(item));
  endtask

  task write_out(input br_ram_data_rd_pipe_item item);
    act_q.push_back(item);
  endtask

  function longint unsigned expected_cycle(input br_ram_data_rd_pipe_item item);
    return item.observed_cycle + longint'(expected_latency_cycles);
  endfunction

  task flush_inflight_expected_for_reset(input longint unsigned reset_cycle);
    if (exp_q.size() == 0) return;

    for (int i = exp_q.size() - 1; i >= 0; i--) begin
      if (expected_cycle(exp_q[i]) < reset_cycle) begin
        continue;
      end
      exp_q.delete(i);
    end
  endtask

  function br_ram_data_rd_pipe_item predict(input br_ram_data_rd_pipe_item in_item);
    br_ram_data_rd_pipe_item predicted_item;

    predicted_item = new(
        in_item.get_width(),
        in_item.valid,
        in_item.depth_tile,
        in_item.id,
        in_item.observed_cycle,
        in_item.observed_time
    );
    predicted_item.copy_word_data(in_item);
    return predicted_item;
  endfunction

  task compare_item(input br_ram_data_rd_pipe_item exp_item,
                    input br_ram_data_rd_pipe_item act_item);
    longint unsigned exp_observed_cycle;

    exp_observed_cycle = expected_cycle(exp_item);
    ctx.check(exp_item.id == act_item.id, $sformatf(
              "%s id mismatch: exp=%0d act=%0d", ScoreboardName, exp_item.id, act_item.id));
    ctx.check(exp_item.get_width() == act_item.get_width(), $sformatf(
              "%s data width mismatch: exp=%0d act=%0d",
              ScoreboardName,
              exp_item.get_width(),
              act_item.get_width()
              ));
    if (exp_item.get_width() == act_item.get_width()) begin
      ctx.check(exp_item.word_data_matches(act_item), $sformatf(
                "%s data mismatch: exp=0b%s act=0b%s",
                ScoreboardName,
                exp_item.word_data_string(),
                act_item.word_data_string()
                ));
    end
    ctx.check(act_item.observed_cycle == exp_observed_cycle, $sformatf(
              "%s latency mismatch: exp_cycle=%0d act_cycle=%0d latency=%0d",
              ScoreboardName,
              exp_observed_cycle,
              act_item.observed_cycle,
              expected_latency_cycles
              ));
  endtask

  task compare_all();
    br_ram_data_rd_pipe_item exp_item;
    br_ram_data_rd_pipe_item act_item;

    while ((exp_q.size() != 0) && (act_q.size() != 0)) begin
      exp_item = exp_q.pop_front();
      act_item = act_q.pop_front();
      compare_item(exp_item, act_item);
    end
  endtask

  task check_empty();
    ctx.check(exp_q.size() == 0, $sformatf(
              "%s has %0d unmatched expected items", ScoreboardName, exp_q.size()));
    ctx.check(act_q.size() == 0, $sformatf(
              "%s has %0d unmatched actual items", ScoreboardName, act_q.size()));
  endtask

  task check_all();
    compare_all();
    check_empty();
  endtask
endclass : br_ram_data_rd_pipe_scoreboard
