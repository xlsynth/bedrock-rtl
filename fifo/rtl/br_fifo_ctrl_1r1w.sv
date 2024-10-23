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

// Bedrock-RTL FIFO Controller (1R1W, Push Ready/Valid, Pop Ready/Valid Variant)
//
// A one-read/one-write (1R1W) FIFO controller that uses the AMBA-inspired
// ready-valid handshake protocol for synchronizing pipeline stages and stalling
// when encountering backpressure hazards.
//
// This module does not include any internal RAM. Instead, it exposes
// read and write ports to an external 1R1W (pseudo-dual-port)
// RAM module, which could be implemented in flops or SRAM.
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
// The RAM interface is required to have a write latency of 1 cycle and a read latency
// of 0 cycles.
//
// See also: br_flow_reg_fwd/br_flow_reg_rev, and br_flow_reg_both, which are optimal
// FIFO implementations for 1 entry and 2 entries, respectively. Use them
// when you know you don't need to parameterize to a greater depth and you don't have
// any use for the status flags.

`include "br_asserts_internal.svh"

module br_fifo_ctrl_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int BitWidth = 1,  // Width of each entry in the FIFO. Must be at least 1.
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

    // Push-side interface
    output logic                push_ready,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    // Pop-side interface
    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [BitWidth-1:0] pop_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // 1R1W RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [ BitWidth-1:0] ram_wr_data,
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    input  logic                 ram_rd_data_valid,
    input  logic [ BitWidth-1:0] ram_rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic bypass_ready;
  logic bypass_valid_unstable;
  logic [BitWidth-1:0] bypass_data_unstable;

  logic ram_push;
  logic ram_pop;

  br_fifo_push_ctrl #(
      .Depth(Depth),
      .BitWidth(BitWidth),
      .EnableBypass(EnableBypass)
  ) br_fifo_push_ctrl (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .bypass_ready,
      // Bypass is only used when EnableBypass is 1.
      .bypass_valid_unstable,  // ri lint_check_waive CONST_ASSIGN
      .bypass_data_unstable,  // ri lint_check_waive CONST_ASSIGN
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_push,
      .ram_pop
  );

  br_fifo_pop_ctrl #(
      .Depth(Depth),
      .BitWidth(BitWidth),
      .EnableBypass(EnableBypass)
  ) br_fifo_pop_ctrl (
      .clk,
      .rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .empty_next,
      .items,
      .items_next,
      // Bypass is only used when EnableBypass is 1.
      .bypass_ready,  // ri lint_check_waive CONST_ASSIGN
      .bypass_valid_unstable,
      .bypass_data_unstable,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data,
      .ram_push,
      .ram_pop
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks
  if (EnableBypass) begin : gen_bypass_impl_checks
    // Check that the datapath has 0 cycle cut-through delay when empty.
    `BR_ASSERT_IMPL(cutthrough_0_delay_a,
                    push_valid && empty |-> pop_valid && pop_data == push_data)
    `BR_ASSERT_IMPL(pop_valid_when_not_empty_or_push_valid_a, pop_valid == (!empty || push_valid))
  end else begin : gen_no_bypass_impl_checks
    // Check that the datapath has 1 cycle cut-through delay when empty.
    `BR_ASSERT_IMPL(cutthrough_1_delay_a,
                    push_valid && empty |=> pop_valid && pop_data == $past(push_data))
    `BR_ASSERT_IMPL(pop_valid_when_not_empty_a, pop_valid == !empty)
  end

  // Check that the backpressure path has 1 cycle delay.
  `BR_ASSERT_IMPL(push_backpressure_when_full_a, full |-> !push_ready)
  `BR_ASSERT_IMPL(backpressure_latency_1_cycle_a, full && pop_ready |=> !full && push_ready)

  // Flag coherence
  `BR_ASSERT_IMPL(items_plus_slots_a, items + slots == Depth)
  `BR_ASSERT_IMPL(items_next_plus_slots_next_a, items_next + slots_next == Depth)
  `BR_ASSERT_IMPL(ram_push_and_ram_pop_flags_unchanged_a,
                  ram_push && ram_pop |-> items_next == items && slots_next == slots)

endmodule : br_fifo_ctrl_1r1w
