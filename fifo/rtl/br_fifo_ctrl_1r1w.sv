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
`include "br_registers.svh"

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
    input logic clk,
    input logic rst,  // Synchronous active-high

    output logic                push_ready,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [BitWidth-1:0] pop_data,

    // Push-side status flags
    output logic full,
    output logic full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    output logic empty,
    output logic empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // 1R1W RAM interface
    output logic wr_valid,
    output logic [AddrWidth-1:0] wr_addr,
    output logic [BitWidth-1:0] wr_data,
    output logic rd_addr_valid,
    output logic [AddrWidth-1:0] rd_addr,
    input logic rd_data_valid,
    input logic [BitWidth-1:0] rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(DepthMustBeAtLeastOne_A, Depth >= 2)
  `BR_ASSERT_STATIC(BitWidthMustBeAtLeastOne_A, BitWidth >= 1)

  // Assert that under push-side backpressure conditions,
  // the pipeline register correctly stalls upstream.
  // That is, on any given cycle, if push_valid is 1 and push_ready
  // is 0, then assert that on the following cycle push_valid is
  // still 1 and push_data has not changed. In other words,
  // we are checking that the input stimulus abides by the push-side
  // ready-valid interface protocol.
  `BR_ASSERT_INTG(push_backpressure_intg_A, !push_ready && push_valid |=> push_valid && $stable
                                            (push_data))
  `BR_ASSERT_INTG(full_intg_C, full)

  `BR_ASSERT_INTG(rd_latency_zero_intg_A, rd_addr_valid |-> rd_data_valid)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic push = push_ready && push_valid;
  logic pop = pop_ready && pop_valid;

  // Push-side logic
  logic [AddrWidth-1:0] wr_addr_next;

  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_wr_addr (
      .clk,
      .rst,
      .incr_valid(push),
      .incr(1'b1),
      .value(wr_addr),
      .value_next(wr_addr_next)
  );

  assign wr_valid = push;
  assign wr_data  = push_data;

  // Pop-side logic
  logic [AddrWidth-1:0] rd_addr_next;

  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_rd_addr (
      .clk,
      .rst,
      .incr_valid(pop),
      .incr(1'b1),
      .value(rd_addr),
      .value_next(rd_addr_next)
  );

  assign rd_valid = pop;
  assign pop_data = rd_data;

  // Status flags
  localparam int InternalCountWidth = $clog2(Depth * 2);
  logic [CountWidth-1:0] wr_minus_rd_next = wr_addr_next - rd_addr_next;

  assign items_next = wr_addr_next >= rd_addr_next ?
    wr_minus_rd_next :
    wr_minus_rd_next + Depth - 1;

  assign slots_next = Depth - items_next;

  assign empty_next = items_next == 0;
  assign full_next = slots_next == 0;

  `BR_REGL(items, items_next, push || pop)
  `BR_REGL(slots, slots_next, push || pop)
  `BR_REGL(full, full_next, push || pop)
  `BR_REGIL(empty, empty_next, push || pop, 1'b1)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(pop_backpressure_A, !pop_ready && pop_valid |=> pop_valid && $stable(pop_data))

  `BR_ASSERT_IMPL(wr_addr_in_range_A, wr_valid |-> wr_addr < Depth)
  `BR_ASSERT_IMPL(rd_addr_in_range_A, rd_addr_valid |-> rd_addr < Depth)

  if (EnableBypass) begin : gen_bypass_impl_checks
    // Check that the datapath has 0 cycle cut-through delay when empty.
    `BR_ASSERT_IMPL(cutthrough_0_delay_A,
                    push_ready && push_valid && empty |-> pop_valid && pop_data == push_data)
    `BR_ASSERT_IMPL(push_ready_when_not_full_or_pop_ready_A, push_ready == (!full || pop_ready))
    `BR_ASSERT_IMPL(pop_valid_when_not_empty_or_push_valid_A, pop_valid == (!empty || push_valid))
  end else begin : gen_no_bypass_impl_checks
    // Check that the datapath has 1 cycle cut-through delay.
    `BR_ASSERT_IMPL(cutthrough_1_delay_A,
                    push_ready && push_valid && empty |=> pop_valid && pop_data == $past(push_data))
    `BR_ASSERT_IMPL(push_ready_when_not_full_A, push_ready == !full)
    `BR_ASSERT_IMPL(pop_valid_when_not_empty_A, pop_valid == !empty)
  end

  // Check that the backpressure path has 1 cycle delay.
  `BR_ASSERT_IMPL(push_backpressure_when_full_A, full |-> !push_ready)
  `BR_ASSERT_IMPL(backpressure_latency_1_cycle_A, full && pop_ready |=> !full && push_ready)

  // Flags
  `BR_ASSERT_IMPL(items_in_range_A, items <= Depth)
  `BR_ASSERT_IMPL(slots_in_range_A, slots <= Depth)
  `BR_ASSERT_IMPL(items_plus_slots_A, items + slots == Depth)
  `BR_ASSERT_IMPL(items_next_plus_slots_next_A, items_next + slots_next == Depth)
  `BR_ASSERT_IMPL(full_A, full == (slots == 0))
  `BR_ASSERT_IMPL(empty_A, empty == (items == 0))
  `BR_ASSERT_IMPL(items_next_A, ##1 items == $past(items_next))
  `BR_ASSERT_IMPL(slots_next_A, ##1 slots == $past(slots_next))
  `BR_ASSERT_IMPL(push_and_pop_flags_unchanged_A,
                  push && pop |-> items_next == items && slots_next == slots)

endmodule : br_fifo_ctrl_1r1w
