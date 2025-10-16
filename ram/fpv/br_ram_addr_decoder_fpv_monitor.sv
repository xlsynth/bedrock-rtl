// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_addr_decoder_fpv_monitor #(
    // Depth of the RAM. Must be at least 1.
    parameter int Depth = 1,
    // Sideband signals to pipeline in lockstep with the address decoding.
    // Safe to tie-off if not used. Must be at least 1.
    parameter int DataWidth = 1,
    // Number of output address tiles. Must be at least 1 and evenly divide Depth.
    parameter int Tiles = 1,
    // Pipeline depth. Must be at least 0.
    // Values greater than 1 are of dubious utility but don't hurt anything.
    parameter int Stages = 0,
    // If 1, then the datapath is implemented. Otherwise, asserts that in_valid is always 0.
    parameter bit EnableDatapath = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int InputAddressWidth = br_math::clamped_clog2(Depth),
    localparam int OutputAddressWidth = br_math::clamped_clog2(TileDepth)
) (
    input logic                                                 clk,
    input logic                                                 rst,
    // Input address and data.
    input logic                                                 in_valid,
    input logic [InputAddressWidth-1:0]                         in_addr,
    input logic                                                 in_data_valid,
    input logic [        DataWidth-1:0]                         in_data,
    // Output tile addresses and data.
    input logic [            Tiles-1:0]                         out_valid,
    input logic [            Tiles-1:0][OutputAddressWidth-1:0] out_addr,
    input logic [            Tiles-1:0]                         out_data_valid,
    input logic [            Tiles-1:0][         DataWidth-1:0] out_data
);

  // ----------FV Modeling Code----------
  localparam int TileWidth = Tiles == 1 ? 1 : $clog2(Tiles);
  logic [TileWidth-1:0] i_pre, i;
  logic [OutputAddressWidth-1:0] fv_out_addr;

  // Pick which tile to send to
  // e.g: Depth = 6, Tiles = 3, then TileDepth = 6/3 = 2
  // in_addr = 0,1 will pick Tile0
  // in_addr = 2,3 will pick Tile1
  // in_addr = 4,5 will pick Tile2
  always_comb begin
    i_pre = 'd0;
    for (int n = 0; n <= TileDepth; n++) begin
      if ((in_addr >= n * TileDepth) && (in_addr < (n + 1) * TileDepth)) begin
        i_pre = n;
        break;
      end
    end
  end

  // if Depth == Tiles:
  //    index of output tile is just in_addr.
  //    out_addr is always 0.
  // Otherwise, out_addr will be in range [0:TileDepth-1]
  assign i = in_valid ? (Depth == Tiles ? in_addr : i_pre) : 'd0;
  assign fv_out_addr = Depth == Tiles ? 'd0 : in_addr - i * TileDepth;

  // ----------FV assumptions----------
  `BR_ASSUME(in_addr_in_range_a, in_valid |-> in_addr < Depth)

  if (!EnableDatapath) begin : gen_no_dp
    `BR_ASSUME(no_in_data_valid_a, !in_data_valid)
    `BR_ASSERT(no_out_data_valid_a, out_data_valid == 'd0)
  end else begin : gen_dp
    `BR_ASSUME(legal_in_data_valid_a, in_data_valid |-> in_valid)
  end

  // ----------FV assertions----------
  `BR_ASSERT(out_valid_onehot_a, $onehot0(out_valid))
  `BR_ASSERT(out_data_valid_onehot_a, $onehot0(out_data_valid))

  if (Stages == 0) begin : gen_no_delay
    `BR_ASSERT(valid_integrity_a, in_valid == out_valid[i])
    `BR_ASSERT(addr_integrity_a, out_valid[i] |-> out_addr[i] == fv_out_addr)

    if (EnableDatapath) begin : gen_dp
      `BR_ASSERT(data_valid_integrity_a, in_data_valid == out_data_valid[i])
      `BR_ASSERT(data_integrity_a, out_data_valid[i] |-> in_data == out_data[i])
    end
  end else begin : gen_delay
    `BR_ASSERT(valid_integrity_a, ##Stages $past(in_valid, Stages) == out_valid[$past(i, Stages)])
    `BR_ASSERT(addr_integrity_a, out_valid[i] |-> out_addr[i] == $past(fv_out_addr, Stages))

    if (EnableDatapath) begin : gen_dp
      `BR_ASSERT(data_valid_integrity_a,
                 ##Stages $past(in_data_valid, Stages) == out_data_valid[$past(i, Stages)])
      `BR_ASSERT(data_integrity_a, out_data_valid[i] |-> $past(in_data, Stages) == out_data[i])
    end
  end


endmodule : br_ram_addr_decoder_fpv_monitor

bind br_ram_addr_decoder br_ram_addr_decoder_fpv_monitor #(
    .Depth(Depth),
    .DataWidth(DataWidth),
    .Tiles(Tiles),
    .Stages(Stages),
    .EnableDatapath(EnableDatapath),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
