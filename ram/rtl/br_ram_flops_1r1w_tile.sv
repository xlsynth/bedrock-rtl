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

// Bedrock-RTL Flop-RAM (1R1W) Tile
//
// A one-read/one-write (1R1W, also known as pseudo-dual-port) flop-based RAM tile.
// The read and write ports may be clocked by different clocks.
// Read latency is zero cycles. Write latency is one cycle.
// By default, write-to-read latency is therefore one cycle.
// If the bypass is enabled, then the write-to-read latency is zero cycles, but
// at the cost of a combinational timing path from the write port to the read port.
// Bypassing is only permissible if the read and write clocks are the same.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_ram_flops_1r1w_tile #(
    parameter int Depth = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    // If 1, allow partial writes to the memory using the wr_word_en signal.
    // If 0, only full writes are allowed and wr_word_en is ignored.
    parameter bit EnablePartialWrite = 0,
    // The width of a word in the memory. This is the smallest unit of data that
    // can be written when partial write is enabled.
    // Must be at least 1 and at most Width.
    // Width must be evenly divisible by WordWidth.
    parameter int WordWidth = Width,
    // If 1, then if the read and write ports access the same address on the same cycle,
    // the write data is forwarded directly to the read data with zero delay.
    // If 0, then if the read and write ports access the same address on the same cycle,
    // then read data is the value stored in the memory prior to the write.
    parameter bit EnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset.
    parameter bit EnableReset = 0,
    // If 1, use structured mux2 gates for the read mux instead of relying on synthesis.
    // This is required if write and read clocks are different.
    parameter bit UseStructuredGates = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int NumWords = Width / WordWidth
) (
    input logic                 wr_clk,
    // Synchronous active-high reset.
    // Reset is always used for assertions. Additionally used for logic only when EnableReset is 1.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic                 wr_rst,
    input logic                 wr_valid,
    input logic [AddrWidth-1:0] wr_addr,
    input logic [    Width-1:0] wr_data,
    input logic [ NumWords-1:0] wr_word_en,

    // Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 rd_clk,
    // Synchronous active-high reset.
    // Read reset is only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 rd_rst,
    input  logic                 rd_addr_valid,
    input  logic [AddrWidth-1:0] rd_addr,
    output logic                 rd_data_valid,
    output logic [    Width-1:0] rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte1_a, Width >= 1)
  `BR_ASSERT_STATIC(no_bypass_with_structured_gates_a, !(EnableBypass && UseStructuredGates))

  `BR_ASSERT_CR_INTG(wr_addr_in_range_A, wr_valid |-> wr_addr < Depth, wr_clk, wr_rst)
  `BR_ASSERT_CR_INTG(rd_addr_in_range_A, rd_addr_valid |-> rd_addr < Depth, rd_clk, rd_rst)

  if (EnablePartialWrite) begin : gen_partial_write_intg_checks
    `BR_ASSERT_STATIC(word_width_in_range_a, (WordWidth >= 1) && (WordWidth <= Width))
    `BR_ASSERT_STATIC(width_divisible_by_word_width_a, (Width % WordWidth) == 0)
  end

  // If EnableBypass is 1 or UseStructuredGates is 0,
  // we must use the same clock for both read and write.
  if (EnableBypass || !UseStructuredGates) begin : gen_same_clock_check
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_INTG(same_clock_a, wr_clk == rd_clk)
  end

  `BR_ASSERT_FINAL(final_not_wr_valid_a, !wr_valid)
  `BR_ASSERT_FINAL(final_not_rd_addr_valid_a, !rd_addr_valid)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Storage flops are on the write clock but read asynchronously
  // from the read clock.
  logic [NumWords-1:0][WordWidth-1:0] mem[Depth];

  // Write port and memory. We avoid the BR_REG* coding style so that certain emulation tools
  // can correctly recognize this behavior as a memory.
  if (EnablePartialWrite) begin : gen_partial_write
    logic [NumWords-1:0][WordWidth-1:0] wr_data_words;

    assign wr_data_words = wr_data;

    if (EnableReset) begin : gen_reset
      always_ff @(posedge wr_clk) begin
        if (wr_rst) begin
          // Loop required over entries since cannot assign a packed type ('0) to an unpacked type (mem).
          for (int i = 0; i < Depth; i++) begin
            mem[i] <= '0;
          end
        end else if (wr_valid) begin
          for (int i = 0; i < NumWords; i++) begin
            if (wr_word_en[i]) begin
              mem[wr_addr][i] <= wr_data_words[i];  // ri lint_check_waive VAR_INDEX_WRITE
            end
          end
        end
      end
    end else begin : gen_no_reset
      always_ff @(posedge wr_clk) begin
        if (wr_valid) begin
          for (int i = 0; i < NumWords; i++) begin
            if (wr_word_en[i]) begin
              mem[wr_addr][i] <= wr_data_words[i];  // ri lint_check_waive VAR_INDEX_WRITE
            end
          end
        end
      end
    end
  end else begin : gen_no_partial_write
    if (EnableReset) begin : gen_reset
      always_ff @(posedge wr_clk) begin
        if (wr_rst) begin
          // Loop required over entries since cannot assign a packed type ('0) to an unpacked type (mem).
          for (int i = 0; i < Depth; i++) begin
            mem[i] <= '0;
          end
        end else if (wr_valid) begin
          mem[wr_addr] <= wr_data;  // ri lint_check_waive VAR_INDEX_WRITE
        end
      end
    end else begin : gen_no_reset
      always_ff @(posedge wr_clk) begin
        if (wr_valid) begin
          mem[wr_addr] <= wr_data;  // ri lint_check_waive VAR_INDEX_WRITE
        end
      end
    end
    `BR_UNUSED(wr_word_en)
  end

  // Read port
  assign rd_data_valid = rd_addr_valid;
  if (UseStructuredGates) begin : gen_structured_read
    // Need to convert memory to packed array
    logic [Depth-1:0][Width-1:0] mem_packed;

    for (genvar i = 0; i < Depth; i++) begin : gen_mem_packed
      assign mem_packed[i] = mem[i];
    end

    br_mux_bin #(
        .NumSymbolsIn(Depth),
        .SymbolWidth(Width),
        .UseStructuredGates(1)
    ) br_mux_bin_inst (
        .select(rd_addr),
        .in(mem_packed),
        .out(rd_data)
    );
  end else begin : gen_behavioral_read
    if (EnableBypass) begin : gen_bypass
      // ri lint_check_waive VAR_INDEX_READ
      assign rd_data = (wr_valid && (wr_addr == rd_addr)) ? wr_data : mem[rd_addr];
    end else begin : gen_no_bypass
      // ri lint_check_waive VAR_INDEX_READ
      assign rd_data = mem[rd_addr];
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(zero_read_latency_A, rd_addr_valid |-> rd_data_valid, rd_clk, rd_rst)
  if (EnableBypass) begin : gen_bypass_impl_checks
    `BR_ASSERT_CR_IMPL(
        bypass_write_to_read_zero_cycles_A,
        wr_valid && rd_addr_valid && (wr_addr == rd_addr) |-> rd_data_valid && rd_data == wr_data,
        rd_clk, rd_rst)
  end

  `BR_ASSERT_FINAL(final_not_rd_data_valid_a, !rd_data_valid)

endmodule : br_ram_flops_1r1w_tile
