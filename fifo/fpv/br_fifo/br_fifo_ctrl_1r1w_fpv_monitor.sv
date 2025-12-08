// SPDX-License-Identifier: Apache-2.0


// FIFO Controller (1R1W, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_ctrl_1r1w_fpv_monitor #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    parameter int RamDepth = Depth,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    localparam int AddrWidth = br_math::clamped_clog2(RamDepth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic                  full,
    input logic                  full_next,
    input logic [CountWidth-1:0] slots,
    input logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    input logic                  empty,
    input logic                  empty_next,
    input logic [CountWidth-1:0] items,
    input logic [CountWidth-1:0] items_next,

    // 1R1W RAM interface
    input logic                 ram_wr_valid,
    input logic [AddrWidth-1:0] ram_wr_addr,
    input logic [    Width-1:0] ram_wr_data,
    input logic                 ram_rd_addr_valid,
    input logic [AddrWidth-1:0] ram_rd_addr,
    input logic                 ram_rd_data_valid,
    input logic [    Width-1:0] ram_rd_data
);

  localparam bit WolperColorEn = 1;
  logic [$clog2(Width)-1:0] magic_bit_index;
  `BR_ASSUME(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < Width))

  // ----------Data Ram FV model----------
  br_fifo_fv_ram #(
      .WolperColorEn(WolperColorEn),
      .NumWritePorts(1),
      .NumReadPorts(1),
      .Depth(RamDepth),
      .Width(Width),
      .RamReadLatency(RamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst,
      .magic_bit_index(magic_bit_index),
      .ram_wr_valid(ram_wr_valid),
      .ram_wr_addr(ram_wr_addr),
      .ram_wr_data(ram_wr_data),
      .ram_rd_addr_valid(ram_rd_addr_valid),
      .ram_rd_addr(ram_rd_addr),
      .ram_rd_data_valid(ram_rd_data_valid),
      .ram_rd_data(ram_rd_data)
  );

  // ----------FIFO basic checks----------
  br_fifo_basic_fpv_monitor #(
      .WolperColorEn(WolperColorEn),
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) br_fifo_basic_fpv_monitor (
      .clk,
      .rst,
      .magic_bit_index,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .empty,
      .empty_next,
      .items,
      .items_next
  );

endmodule : br_fifo_ctrl_1r1w_fpv_monitor

bind br_fifo_ctrl_1r1w br_fifo_ctrl_1r1w_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .EnableBypass(EnableBypass),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RamReadLatency(RamReadLatency),
    .RamDepth(RamDepth),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability)
) monitor (.*);
