// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_ram_initializer_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    localparam int AddressWidth = $clog2(Depth)
) (
    input logic clk,
    input logic rst,
    // The value to write into each entry of the RAM.
    input logic [Width-1:0] initial_value,
    // Starts the initialization process. The first write occurs on the next clock cycle.
    // Start is ignored while busy is high.
    input logic start,
    // Busy is asserted while initialization is in progress.
    // While busy, the user is responsible for ensuring that:
    // 1) the RAM write-port is exclusively driven by the br_ram_initializer
    // 2) there are no write address conflicts with any other write ports
    // 3) the initial_value is stable
    input logic busy,
    // RAM write-port interface.
    input logic wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [Width-1:0] wr_data
);

  // ----------FV modeling code----------
  logic [AddressWidth-1:0] fv_addr;
  logic fv_done;
  logic fv_busy;

  assign fv_done = (fv_addr == Depth - 'd1);
  `BR_REGL(fv_busy, fv_done ? 1'b0 : 1'b1, start | fv_done)
  `BR_REGL(fv_addr, fv_busy ? (fv_addr + 'd1) : 'd0, fv_busy | start)

  // ----------FV assumptions----------
  `BR_ASSUME(initial_value_stable_a, busy |-> $stable(initial_value))

  // ----------FV assertions----------
  `BR_ASSERT(wr_valid_a, busy |-> wr_valid)
  `BR_ASSERT(wr_addr_a, busy |-> wr_addr == fv_addr)
  `BR_ASSERT(wr_data_a, busy |-> wr_data == initial_value)

  `BR_ASSERT(busy_a, fv_busy == busy)
  `BR_ASSERT(busy_start_a, start & !busy |=> busy)
  `BR_ASSERT(busy_end_a, start & !busy |=> ##Depth !busy)

endmodule : br_ram_initializer_fpv_monitor

bind br_ram_initializer br_ram_initializer_fpv_monitor #(
    .Depth(Depth),
    .Width(Width)
) monitor (.*);
