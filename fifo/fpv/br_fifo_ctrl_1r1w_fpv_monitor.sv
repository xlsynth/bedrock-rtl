// Copyright 2024-2025 The Bedrock-RTL Authors
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

// FIFO Controller (1R1W, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_ctrl_1r1w_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit EnableBypass = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    // The actual depth of the RAM. This may be smaller than the FIFO depth
    // if EnableBypass is 1 and RamReadLatency is >0 or RegisterPopOutputs is 1.
    // The minimum RAM depth would be (Depth - RamReadLatency - 1) or 1
    // if Depth is less than or equal to RamReadLatency + 1.
    // If bypass is disabled or RamReadLatency and RegisterPopOutputs are both 0,
    // the minimum RAM depth is Depth.
    // The RAM depth may be made larger than the minimum if convenient (e.g. the
    // backing RAM is an SRAM of slightly larger depth than the FIFO depth).
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

  // ----------FV Modeling Code----------
  logic [RamDepth-1:0][Width-1:0] fv_ram_data;

  `BR_REGLN(fv_ram_data[ram_wr_addr], ram_wr_data, ram_wr_valid)

  // ----------FV assumptions----------
  if (RamReadLatency == 0) begin : gen_latency0
    `BR_ASSUME(ram_rd_data_a, ram_rd_data == fv_ram_data[ram_rd_addr])
    `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid == ram_rd_addr_valid)
  end else begin : gen_latency_non0
    `BR_ASSUME(ram_rd_data_a, ram_rd_data == fv_ram_data[$past(ram_rd_addr, RamReadLatency)])
    `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid == $past(
               ram_rd_addr_valid, RamReadLatency))
  end

  // ----------FIFO basic checks----------
  br_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) br_fifo_basic_fpv_monitor (
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
