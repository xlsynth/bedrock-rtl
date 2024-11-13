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

// Bedrock-RTL Flop-RAM (1R1W)
//
// A one-read/one-write (1R1W, also known as pseudo-dual-port) flop-based RAM
// that is constructed out of pipelined tiles.
//
// Parameterized write, read, and read-after-write hazard latencies.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w #(
    parameter int Depth = 2,  // Must be at least 2
    parameter int BitWidth = 1,  // Must be at least 1
    parameter int WriteLatency = 1,  // Must be at least 1
    parameter int ReadLatency = 0,  // Must be at least 0
    parameter int RowTiles = 1,  // TODO
    parameter int ColTiles = 1,  // TODO
    parameter bit TileEnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset.
    parameter bit EnableReset = 0,
    localparam int ReadAfterWriteHazardLatency = TileEnableBypass ? 0 : 1,
    localparam int AddrWidth = $clog2(Depth)
) (
    input  logic                 clk,
    // Synchronous active-high reset.
    // Reset is always used for assertions. Additionally used for logic only when EnableReset is 1.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 rst,
    input  logic                 wr_valid,
    input  logic [AddrWidth-1:0] wr_addr,
    input  logic [ BitWidth-1:0] wr_data,
    input  logic                 rd_addr_valid,
    input  logic [AddrWidth-1:0] rd_addr,
    output logic                 rd_data_valid,
    output logic [ BitWidth-1:0] rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(write_latency_gte_1_a, WriteLatency >= 1)
  `BR_ASSERT_STATIC(read_latency_gte_0_a, ReadLatency >= 0)
  // TODO(mgottscho): Write more
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // TODO(mgottscho): Implement

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(read_latency_A, rd_addr_valid |-> ##ReadLatency rd_data_valid)
  // TODO(mgottscho): Write more
  // Rely on submodule implementation checks

endmodule : br_ram_flops_1r1w
