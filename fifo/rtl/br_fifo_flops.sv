// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL FIFO (Internal 1R1W Flop-RAM, Push Ready/Valid, Pop Ready/Valid Variant)
//
// A one-read/one-write (1R1W) FIFO that uses the AMBA-inspired
// ready-valid handshake protocol for synchronizing pipeline stages and stalling
// when encountering backpressure hazards.
//
// This module includes an internal flop-RAM.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// The FIFO can be parameterized in bypass mode or non-bypass mode.
// In bypass mode (default), then pushes forward directly to the pop
// interface when the FIFO is empty, resulting in a cut-through latency of 0 cycles.
// This comes at the cost of a combinational timing path from the push
// interface to the pop interface. Conversely, when bypass is disabled,
// then pushes always go through the RAM before they can become
// visible at the pop interface. This results in a cut-through latency of
// 1 cycle, but improves static timing by eliminating any combinational paths
// from push to pop.
//
// Bypass is enabled by default to minimize latency accumulation throughout a design.
// It is recommended to disable the bypass only when necessary to close timing.
//
// See also: br_flow_reg_fwd/br_flow_reg_rev, and br_flow_reg_both, which are optimal
// FIFO implementations for 1 entry and 2 entries, respectively. Use them
// when you know you don't need to parameterize to a greater depth and you don't have
// any use for the status flags.

module br_fifo_flops #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then bypasses push-to-pop when the FIFO is empty, resulting in
    // a cut-through latency of 0 cycles, but at the cost of worse timing.
    // If 0, then pushes always go through the RAM before they can become
    // visible at the pop interface. This results in a cut-through latency of
    // 1 cycle, but timing is improved.
    parameter bit EnableBypass = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Push-side status flags
    output logic full,
    output logic full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    output logic empty,
    output logic empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic ram_wr_valid;
  logic [AddrWidth-1:0] ram_wr_addr;
  logic [Width-1:0] ram_wr_data;
  logic ram_rd_addr_valid;
  logic [AddrWidth-1:0] ram_rd_addr;
  logic ram_rd_data_valid;
  logic [Width-1:0] ram_rd_data;

  br_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass)
  ) br_fifo_ctrl_1r1w (
      .clk,
      .rst,
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
      .items_next,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data
  );

  br_ram_flops_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .TileEnableBypass(0),
      .EnableReset(0)
  ) br_ram_flops_1r1w (
      .clk,
      .rst,
      .wr_valid(ram_wr_valid),
      .wr_addr(ram_wr_addr),
      .wr_data(ram_wr_data),
      .rd_addr_valid(ram_rd_addr_valid),
      .rd_addr(ram_rd_addr),
      .rd_data_valid(ram_rd_data_valid),
      .rd_data(ram_rd_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_fifo_flops
