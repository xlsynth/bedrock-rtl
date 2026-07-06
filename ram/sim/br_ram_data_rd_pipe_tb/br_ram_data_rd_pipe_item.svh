// SPDX-License-Identifier: Apache-2.0

typedef logic br_ram_data_rd_pipe_data_bit_t;

class br_ram_data_rd_pipe_item extends br_item;
  // Interface valid value represented by this item.
  bit valid;
  // Selected depth row for input traffic; zero for output traffic.
  int unsigned depth_tile;
  // Full-width word size for this item.
  int unsigned width;
  // Full-width word driven into or observed from the pipe, sized from the TB Width parameter.
  br_ram_data_rd_pipe_data_bit_t word_data[int unsigned];
  // Monotonic transaction index assigned by monitors.
  longint unsigned id;
  // Clock cycle when the monitor observed this item.
  longint unsigned observed_cycle;
  // Simulation time when the monitor observed this item.
  time observed_time;

  function new(input int unsigned width = 0, input bit valid = 1'b0,
               input int unsigned depth_tile = 0, input longint unsigned id = 0,
               input longint unsigned observed_cycle = 0, input time observed_time = 0);
    super.new("br_ram_data_rd_pipe_item");
    this.valid = valid;
    this.depth_tile = depth_tile;
    set_width(width);
    this.id = id;
    this.observed_cycle = observed_cycle;
    this.observed_time = observed_time;
  endfunction

  function void set_width(input int unsigned width);
    this.width = width;
    clear_word_data();
  endfunction

  function int unsigned get_width();
    return width;
  endfunction

  function void clear_word_data();
    word_data.delete();
    for (int unsigned i = 0; i < width; i++) begin
      word_data[i] = 1'b0;
    end
  endfunction

  function void copy_word_data(input br_ram_data_rd_pipe_item item);
    set_width(item.get_width());
    for (int unsigned i = 0; i < width; i++) begin
      word_data[i] = item.word_data[i];
    end
  endfunction

  function bit word_data_matches(input br_ram_data_rd_pipe_item item);
    if (width != item.get_width()) return 1'b0;

    for (int unsigned i = 0; i < width; i++) begin
      if (word_data[i] !== item.word_data[i]) return 1'b0;
    end
    return 1'b1;
  endfunction

  function bit word_data_is_zero();
    for (int unsigned i = 0; i < width; i++) begin
      if (word_data[i] !== 1'b0) return 1'b0;
    end
    return 1'b1;
  endfunction

  function string word_data_string();
    string text;

    text = "";
    for (int i = int'(width); i > 0; i--) begin
      text = {text, $sformatf("%0b", word_data[i-1])};
    end
    return text;
  endfunction

endclass : br_ram_data_rd_pipe_item
