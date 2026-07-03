// SPDX-License-Identifier: Apache-2.0

class br_ram_addr_decoder_item extends br_item;
  // Payload captured from a monitor stream or driven on the input data stream.
  rand logic [63:0] data;
  // Address driven by the combined input sequence and driver.
  rand logic [63:0] addr;
  // Set when the driver should present addr with address valid high.
  rand bit has_addr;
  // Set when data should be driven on the input data stream.
  rand bit has_data;
  // Set when tile metadata is meaningful for this item.
  bit has_tile;
  // Output lane observed by the monitor; ignored when has_tile is clear.
  int unsigned tile;
  // Monotonic transaction index assigned by the monitor that observed this item.
  longint unsigned id;
  // Simulation time when the monitor observed this item.
  time observed_time;
  // Clock cycle when the monitor observed this item; used for latency checks.
  longint unsigned observed_cycle;

  function new(input logic [63:0] data = '0, input bit has_tile = 1'b0, input int unsigned tile = 0,
               input longint unsigned id = 0, input time observed_time = 0,
               input longint unsigned observed_cycle = 0, input logic [63:0] addr = '0,
               input bit has_addr = 1'b0, input bit has_data = 1'b1);
    super.new("br_ram_addr_decoder_item");
    this.data = data;
    this.addr = addr;
    this.has_addr = has_addr;
    this.has_data = has_data;
    this.has_tile = has_tile;
    this.tile = tile;
    this.id = id;
    this.observed_time = observed_time;
    this.observed_cycle = observed_cycle;
  endfunction
endclass : br_ram_addr_decoder_item
