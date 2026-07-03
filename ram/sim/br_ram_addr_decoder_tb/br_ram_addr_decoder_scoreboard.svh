// SPDX-License-Identifier: Apache-2.0

typedef enum {
  BrRamAddrDecoderIn,
  BrRamAddrDecoderOut
} br_ram_addr_decoder_scoreboard_port_e;

typedef br_dv_port_sink#(
    .ItemType(br_ram_addr_decoder_item),
    .PortType(br_ram_addr_decoder_scoreboard_port_e)
) br_ram_addr_decoder_scoreboard_sink_t;

class br_ram_addr_decoder_scoreboard extends br_dv_port_sink_target #(
    .ItemType(br_ram_addr_decoder_item),
    .PortType(br_ram_addr_decoder_scoreboard_port_e)
);
  localparam string ScoreboardName = "br_ram_addr_decoder";

  local int tile_depth;
  local int expected_latency_cycles;
  local br_ram_addr_decoder_item exp_q[$];
  local br_ram_addr_decoder_item act_q[$];
  local br_ram_addr_decoder_scoreboard_sink_t in_sink;
  local br_ram_addr_decoder_scoreboard_sink_t out_sink;

  function new(input br_dv_context ctx = null, input int tile_depth = 1,
               input int expected_latency_cycles = 0);
    super.new(ctx);
    this.tile_depth = tile_depth;
    this.expected_latency_cycles = expected_latency_cycles;
    if (ctx != null) begin
      ctx.register(this);
    end
    in_sink  = new(this, BrRamAddrDecoderIn);
    out_sink = new(this, BrRamAddrDecoderOut);
  endfunction

  virtual function br_dv_component_kind_e get_kind();
    return BrDvScoreboard;
  endfunction

  function br_ram_addr_decoder_scoreboard_sink_t get_sink(
      input br_ram_addr_decoder_scoreboard_port_e port);
    case (port)
      BrRamAddrDecoderIn: return in_sink;
      BrRamAddrDecoderOut: return out_sink;
      default: return null;
    endcase
  endfunction

  task write_port(input br_ram_addr_decoder_scoreboard_port_e port,
                  input br_ram_addr_decoder_item item);
    case (port)
      BrRamAddrDecoderIn: write_in(item);
      BrRamAddrDecoderOut: write_out(item);
      default: ctx.check(1'b0, $sformatf("%s unknown write port %0d", ScoreboardName, port));
    endcase
  endtask

  task write_in(input br_ram_addr_decoder_item item);
    ctx.check(item.has_addr, $sformatf(
              "%s input item id=%0d is missing address", ScoreboardName, item.id));
    exp_q.push_back(predict(item));
  endtask

  task write_out(input br_ram_addr_decoder_item item);
    act_q.push_back(item);
  endtask

  function br_ram_addr_decoder_item predict(input br_ram_addr_decoder_item in_item);
    longint unsigned tile;
    longint unsigned local_addr;
    br_ram_addr_decoder_item predicted_item;

    tile = in_item.addr / tile_depth;
    local_addr = in_item.addr % tile_depth;
    predicted_item = new(
        in_item.data,
        1'b1,
        int'(tile),
        in_item.id,
        in_item.observed_time,
        in_item.observed_cycle,
        64'(local_addr),
        1'b1,
        in_item.has_data
    );
    return predicted_item;
  endfunction

  task compare_item(input br_ram_addr_decoder_item exp_item,
                    input br_ram_addr_decoder_item act_item);
    ctx.check(exp_item.id == act_item.id, $sformatf(
              "%s id mismatch: exp=%0d act=%0d", ScoreboardName, exp_item.id, act_item.id));
    ctx.check(act_item.has_addr, $sformatf("%s actual item is missing address", ScoreboardName));
    ctx.check(
        exp_item.addr === act_item.addr, $sformatf(
        "%s address mismatch: exp=0x%0h act=0x%0h", ScoreboardName, exp_item.addr, act_item.addr));
    ctx.check(exp_item.has_data == act_item.has_data, $sformatf(
              "%s has_data mismatch: exp=%0b act=%0b",
              ScoreboardName,
              exp_item.has_data,
              act_item.has_data
              ));
    if (exp_item.has_data) begin
      ctx.check(
          exp_item.data === act_item.data, $sformatf(
          "%s data mismatch: exp=0x%0h act=0x%0h", ScoreboardName, exp_item.data, act_item.data));
    end
    ctx.check(act_item.has_tile, $sformatf("%s actual item is missing tile", ScoreboardName));
    ctx.check(exp_item.tile == act_item.tile, $sformatf(
              "%s tile mismatch: exp=%0d act=%0d", ScoreboardName, exp_item.tile, act_item.tile));
    ctx.check(act_item.observed_cycle == (exp_item.observed_cycle + expected_latency_cycles),
              $sformatf(
              "%s latency mismatch: exp_cycle=%0d act_cycle=%0d latency=%0d",
              ScoreboardName,
              exp_item.observed_cycle + expected_latency_cycles,
              act_item.observed_cycle,
              expected_latency_cycles
              ));
  endtask

  task compare_all();
    br_ram_addr_decoder_item exp_item;
    br_ram_addr_decoder_item act_item;

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
endclass : br_ram_addr_decoder_scoreboard
