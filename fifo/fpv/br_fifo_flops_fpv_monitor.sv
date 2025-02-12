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

// FIFO (Internal 1R1W Flop-RAM, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_flops_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit EnableBypass = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int FlopRamDepthTiles = 1,
    parameter int FlopRamWidthTiles = 1,
    parameter int FlopRamAddressDepthStages = 0,
    parameter int FlopRamReadDataDepthStages = 0,
    parameter int FlopRamReadDataWidthStages = 0,
    localparam int AddrWidth = $clog2(Depth),
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
    input logic [CountWidth-1:0] items_next
);

  br_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass)
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

endmodule : br_fifo_flops_fpv_monitor

bind br_fifo_flops br_fifo_flops_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .EnableBypass(EnableBypass),
    .RegisterPopOutputs(RegisterPopOutputs),
    .FlopRamDepthTiles(FlopRamDepthTiles),
    .FlopRamWidthTiles(FlopRamWidthTiles),
    .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
    .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
    .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages)
) monitor (.*);
