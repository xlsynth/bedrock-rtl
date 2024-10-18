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
// A one-read/one-write (1R1W, also known as pseudo-dual-port) flop-based RAM.
// Read latency is zero cycles. Write latency is one cycle.
// By default, write-to-read latency is therefore one cycle.
// If the bypass is enabled, then the write-to-read latency is zero cycles, but
// at the cost of a combinational timing path from the write port to the read port.
// The internal flop-RAM does not get reset.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_ram_flops_1r1w #(
    parameter int Depth = 2,  // Must be at least 2
    parameter int BitWidth = 1,  // Must be at least 1
    // If 1, then if the read and write ports access the same address on the same cycle,
    // the write data is forwarded directly to the read data with zero delay.
    // If 0, then if the read and write ports access the same address on the same cycle,
    // then read data is the value stored in the memory prior to the write.
    parameter bit EnableBypass = 0,
    // If 1, then the memory elements are cleared to 0 upon reset.
    parameter bit EnableReset = 0,
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
  `BR_ASSERT_STATIC(depth_gte2_a, Depth >= 2)
  `BR_ASSERT_STATIC(bitwidth_gte1_a, BitWidth >= 1)

  `BR_ASSERT_INTG(wr_addr_in_range_A, wr_valid |-> wr_addr < Depth)
  `BR_ASSERT_INTG(rd_addr_in_range_A, rd_addr_valid |-> rd_addr < Depth)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [Depth-1:0][BitWidth-1:0] mem;

  // Write port
  for (genvar i = 0; i < Depth; i++) begin : gen_flops
    if (EnableReset) begin : gen_reset
      `BR_REGL(mem[i], wr_data, wr_valid && (wr_addr == i))
    end else begin : gen_no_reset
      `BR_REGLN(mem[i], wr_data, wr_valid && (wr_addr == i))
    end
  end

  // Read port
  assign rd_data_valid = rd_addr_valid;
  if (EnableBypass) begin : gen_bypass
    // ri lint_check_waive VAR_INDEX_READ
    assign rd_data = (wr_valid && (wr_addr == rd_addr)) ? wr_data : mem[rd_addr];
  end else begin : gen_no_bypass
    // ri lint_check_waive VAR_INDEX_READ
    assign rd_data = mem[rd_addr];
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(zero_read_latency_A, rd_addr_valid |-> rd_data_valid)
  if (EnableBypass) begin : gen_bypass_impl_checks
    `BR_ASSERT_IMPL(
        bypass_write_to_read_zero_cycles_A,
        wr_valid && rd_addr_valid && wr_addr == rd_addr |-> rd_data_valid && rd_data == wr_data)
  end else begin : gen_bypass_impl_checks
    `BR_ASSERT_IMPL(no_bypass_write_to_read_one_cycle_A,
                    rd_addr_valid && $past(
                        wr_valid
                    ) && rd_addr == $past(
                        wr_addr
                    ) |-> rd_data_valid && rd_data == $past(
                        wr_data
                    ))
  end

endmodule : br_ram_flops_1r1w
