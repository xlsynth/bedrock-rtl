// SPDX-License-Identifier: Apache-2.0

typedef enum int {
  BrRamDataRdPipeValidRandom = -1,
  BrRamDataRdPipeValidIdle = 0,
  BrRamDataRdPipeValidActive = 1,
  BrRamDataRdPipeValidBubblePattern
} br_ram_data_rd_pipe_valid_mode_e;

typedef enum int {
  BrRamDataRdPipeDepthRandom,
  BrRamDataRdPipeDepthRoundRobin
} br_ram_data_rd_pipe_depth_mode_e;

typedef enum int {
  BrRamDataRdPipePayloadRandom,
  BrRamDataRdPipePayloadTilePattern,
  BrRamDataRdPipePayloadWalkingOne
} br_ram_data_rd_pipe_payload_mode_e;

class br_ram_data_rd_pipe_random_sequence #(
    parameter int Width = 1,
    parameter int DepthTiles = 1,
    parameter int WidthTiles = 1
) extends br_dv_sequence #(
    .ItemType(br_ram_data_rd_pipe_item)
);
  function new(input br_dv_context ctx = null);
    super.new(ctx);
  endfunction

  function void fill_random_payload(input br_ram_data_rd_pipe_item item);
    int unsigned rand_word;

    item.clear_word_data();
    for (int bit_idx = 0; bit_idx < Width; bit_idx += 32) begin
      rand_word = $urandom();
      for (int b = 0; (b < 32) && ((bit_idx + b) < Width); b++) begin
        item.word_data[bit_idx+b] = rand_word[b];
      end
    end
  endfunction

  function void fill_tile_pattern_payload(input br_ram_data_rd_pipe_item item,
                                          input int unsigned item_index);
    int tile_width;

    tile_width = (Width + WidthTiles - 1) / WidthTiles;
    item.clear_word_data();
    for (int w = 0; w < WidthTiles; w++) begin
      for (int b = 0; (b < tile_width) && (((w * tile_width) + b) < Width); b++) begin
        item.word_data[(w*tile_width)+b] = bit'((w + item_index + 1) >> (b % 8));
      end
    end
  endfunction

  function void fill_walking_one_payload(input br_ram_data_rd_pipe_item item,
                                         input int unsigned item_index);
    item.clear_word_data();
    item.word_data[item_index%Width] = 1'b1;
  endfunction

  function void fill_item_payload(
      input br_ram_data_rd_pipe_item item,
      input br_ram_data_rd_pipe_payload_mode_e payload_mode = BrRamDataRdPipePayloadRandom,
      input int unsigned item_index = 0);
    case (payload_mode)
      BrRamDataRdPipePayloadTilePattern: fill_tile_pattern_payload(item, item_index);
      BrRamDataRdPipePayloadWalkingOne: fill_walking_one_payload(item, item_index);
      default: fill_random_payload(item);
    endcase
  endfunction

  function bit select_valid(input br_ram_data_rd_pipe_valid_mode_e valid_mode,
                            input int unsigned item_index);
    case (valid_mode)
      BrRamDataRdPipeValidIdle: return 1'b0;
      BrRamDataRdPipeValidActive: return 1'b1;
      BrRamDataRdPipeValidBubblePattern: return (item_index % 5) inside {0, 2, 3};
      default: return bit'($urandom_range(0, 1));
    endcase
  endfunction

  function int unsigned select_depth_tile(input br_ram_data_rd_pipe_depth_mode_e depth_mode,
                                          input int unsigned item_index);
    case (depth_mode)
      BrRamDataRdPipeDepthRoundRobin: return item_index % DepthTiles;
      default: return $urandom_range(0, DepthTiles - 1);
    endcase
  endfunction

  task fill_random(
      input int unsigned num_items,
      input br_ram_data_rd_pipe_valid_mode_e valid_mode = BrRamDataRdPipeValidRandom,
      input br_ram_data_rd_pipe_depth_mode_e depth_mode = BrRamDataRdPipeDepthRandom,
      input br_ram_data_rd_pipe_payload_mode_e payload_mode = BrRamDataRdPipePayloadRandom);
    br_ram_data_rd_pipe_item item;

    for (int unsigned i = 0; i < num_items; i++) begin
      item = new(Width);
      item.valid = select_valid(valid_mode, i);
      item.depth_tile = select_depth_tile(depth_mode, i);
      fill_item_payload(item, payload_mode, i);
      if ((valid_mode == BrRamDataRdPipeValidIdle) && item.word_data_is_zero()) begin
        item.word_data[0] = 1'b1;
      end
      push_item(item);
    end
  endtask

endclass : br_ram_data_rd_pipe_random_sequence
