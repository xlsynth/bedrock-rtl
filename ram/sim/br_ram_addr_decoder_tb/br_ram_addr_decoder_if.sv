// SPDX-License-Identifier: Apache-2.0

interface br_ram_addr_decoder_if #(
    parameter int Tiles = 1,
    parameter int Width = 1
);
  logic [Tiles-1:0]            valid;
  logic [Tiles-1:0][Width-1:0] data;
endinterface : br_ram_addr_decoder_if
