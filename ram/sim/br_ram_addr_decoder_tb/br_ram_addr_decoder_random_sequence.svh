// SPDX-License-Identifier: Apache-2.0

class br_ram_addr_decoder_random_sequence #(
    parameter longint unsigned MaxAddressValue = 64'hffff_ffff_ffff_ffff
) extends br_dv_sequence #(
    .ItemType(br_ram_addr_decoder_item)
);
  function new(input br_dv_context ctx = null);
    super.new(ctx);
  endfunction

  task fill_random(input int unsigned num_items, input bit allow_data = 1'b1);
    br_ram_addr_decoder_item item;
    int randomize_status;

    repeat (num_items) begin
      item = new();
      randomize_status = item.randomize() with {
        addr <= MaxAddressValue;
        if (!has_addr) {has_data == 1'b0;}
        if (!allow_data) {has_data == 1'b0;}
      };
      ctx.check(randomize_status != 0, "failed to randomize br_ram_addr_decoder_item");
      push_item(item);
    end
  endtask
endclass : br_ram_addr_decoder_random_sequence
