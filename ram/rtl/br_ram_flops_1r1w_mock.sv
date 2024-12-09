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

// Bedrock-RTL Flop-RAM (1R1W) -- MOCK
//
// A **MOCK** implementation of a one-read/one-write (1R1W, also known as pseudo-dual-port) flop-RAM.
// Behaves identically to br_ram_flops_1r1w, but omits unnecessary implementation details that are
// only relevant for physical design.
//
// Not intended for synthesis (doesn't actually implement tiling or hierarchical address decoding).

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w_mock #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    // Number of tiles along the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int DepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int WidthTiles = 1,
    // Number of pipeline register stages inserted along the write address and read address paths
    // in the depth dimension. Must be at least 0.
    parameter int AddressDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the depth dimension.
    // Must be at least 0.
    parameter int ReadDataDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the width dimension.
    // Must be at least 0.
    parameter int ReadDataWidthStages = 0,
    // If 1, then each memory tile has a read-after-write hazard latency of 0 cycles, i.e.,
    // if the tile read and write address are valid and equal on the same cycle then the tile
    // read data equals the tile write data.
    // If 0, then each memory tile has a read-after-write hazard latency of 1 cycle, i.e.,
    // a read cannot observe previously written data unless the read address is issued at least
    // one cycle after the write.
    // Bypassing is only permissible if the read and write clocks are the same.
    parameter bit TileEnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset. Otherwise, they are undefined until
    // written for the first time.
    parameter bit EnableMemReset = 0,
    localparam int AddressWidth = $clog2(Depth),
    // Write latency in units of wr_clk cycles
    // ri lint_check_waive PARAM_NOT_USED
    localparam int WriteLatency = AddressDepthStages + 1,
    // Read latency in units of rd_clk cycles
    localparam int ReadLatency = AddressDepthStages + ReadDataDepthStages + ReadDataWidthStages
) (
    // Write-clock signals
    // Posedge-triggered clock.
    input logic                    wr_clk,
    // Synchronous active-high reset.
    // Reset is not used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic                    wr_rst,
    input logic                    wr_valid,
    input logic [AddressWidth-1:0] wr_addr,
    input logic [       Width-1:0] wr_data,

    // Read-clock signals
    // Posedge-triggered clock.
    // The clock may not be used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                    rd_clk,
    // Synchronous active-high reset.
    // Reset is not used if all stages are 0, hence lint waiver.
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                    rd_rst,
    input  logic                    rd_addr_valid,
    input  logic [AddressWidth-1:0] rd_addr,
    output logic                    rd_data_valid,
    output logic [       Width-1:0] rd_data
);

  localparam int TileDepth = br_math::ceil_div(Depth, DepthTiles);
  localparam int TileWidth = br_math::ceil_div(Width, WidthTiles);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  // DepthTiles checks
  `BR_ASSERT_STATIC(depth_tiles_gte1_a, DepthTiles >= 1)
  `BR_ASSERT_STATIC(depth_tiles_evenly_divides_depth_a, (DepthTiles * TileDepth) == Depth)

  // WidthTiles checks
  `BR_ASSERT_STATIC(width_tiles_gte1_a, WidthTiles >= 1)
  `BR_ASSERT_STATIC(width_tiles_evenly_divides_width_a, (WidthTiles * TileWidth) == Width)

  // Address stages checks
  `BR_ASSERT_STATIC(address_depth_stages_gte0_a, AddressDepthStages >= 0)

  // Read data stages checks
  `BR_ASSERT_STATIC(read_data_depth_stages_gte0_a, ReadDataDepthStages >= 0)
  `BR_ASSERT_STATIC(read_data_width_stages_gte0_a, ReadDataWidthStages >= 0)

  // Address range checks
  `BR_ASSERT_CR_INTG(wr_addr_in_range_a, wr_valid |-> wr_addr < Depth, wr_clk, wr_rst)
  `BR_ASSERT_CR_INTG(rd_addr_in_range_a, rd_addr_valid |-> rd_addr < Depth, rd_clk, rd_rst)

  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic mem_wr_valid;
  logic [AddressWidth-1:0] mem_wr_addr;
  logic [Width-1:0] mem_wr_data;
  logic mem_rd_addr_valid;
  logic mem_rd_data_valid;
  logic [AddressWidth-1:0] mem_rd_addr;
  logic [Width-1:0] mem_rd_data;
  logic [Depth-1:0][Width-1:0] mem;

  br_delay_valid #(
      .Width(AddressWidth + Width),
      .NumStages(AddressDepthStages)
  ) br_delay_valid_wr (
      .clk(wr_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rst(wr_rst),
      .in_valid(wr_valid),
      .in({wr_addr, wr_data}),
      .out_valid(mem_wr_valid),
      .out({mem_wr_addr, mem_wr_data}),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  br_delay_valid #(
      .Width(AddressWidth),
      .NumStages(AddressDepthStages)
  ) br_delay_valid_rd_addr (
      .clk(rd_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rst(rd_rst),
      .in_valid(rd_addr_valid),
      .in(rd_addr),
      .out_valid(mem_rd_addr_valid),
      .out(mem_rd_addr),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  // Write port and memory. We avoid the BR_REG* coding style so that certain emulation tools
  // can correctly recognize this behavior as a memory.
  if (EnableMemReset) begin : gen_reset
    always_ff @(posedge wr_clk) begin
      if (wr_rst) begin
        // Loop required over entries since cannot assign a packed type ('0) to an unpacked type (mem).
        for (int i = 0; i < Depth; i++) begin
          mem[i] <= '0;
        end
      end else if (mem_wr_valid) begin
        mem[mem_wr_addr] <= mem_wr_data;  // ri lint_check_waive VAR_INDEX_WRITE
      end
    end
  end else begin : gen_no_reset
    always_ff @(posedge wr_clk) begin
      if (mem_wr_valid) begin
        mem[mem_wr_addr] <= mem_wr_data;  // ri lint_check_waive VAR_INDEX_WRITE
      end
    end
  end

  // Read port
  assign mem_rd_data_valid = mem_rd_addr_valid;
  if (TileEnableBypass) begin : gen_bypass
    // ri lint_check_waive VAR_INDEX_READ
    assign mem_rd_data =
      (mem_wr_valid && (mem_wr_addr == mem_rd_addr)) ? mem_wr_data : mem[mem_rd_addr];
  end else begin : gen_no_bypass
    // ri lint_check_waive VAR_INDEX_READ
    assign mem_rd_data = mem[mem_rd_addr];
  end

  br_delay_valid #(
      .Width(Width),
      .NumStages(ReadDataDepthStages + ReadDataWidthStages)
  ) br_delay_valid_rd_data (
      .clk(rd_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rst(rd_rst),
      .in_valid(mem_rd_data_valid),
      .in(mem_rd_data),
      .out_valid(rd_data_valid),
      .out(rd_data),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(read_latency_a, rd_addr_valid |-> ##ReadLatency rd_data_valid, rd_clk, rd_rst)

  if (TileEnableBypass) begin : gen_bypass_checks
    if (ReadLatency > 0) begin : gen_readlat_gt0
      `BR_ASSERT_CR_IMPL(read_write_hazard_gets_new_data_a,
                         wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          ##ReadLatency rd_data_valid && rd_data == $past(
                             wr_data, ReadLatency
                         ),
                         rd_clk, rd_rst)
    end else begin : gen_readlat_eq0
      `BR_ASSERT_CR_IMPL(read_write_hazard_gets_new_data_a,
                         wr_valid && rd_addr_valid && (wr_addr == rd_addr) |->
          rd_data_valid && (rd_data == wr_data),
                         rd_clk, rd_rst)
    end
  end

endmodule : br_ram_flops_1r1w_mock
