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

// Bedrock-RTL FIFO Pop Controller (Ready/Valid)

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_fifo_pop_ctrl #(
    parameter int Depth = 2,
    parameter int BitWidth = 1,
    parameter bit EnableBypass = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [BitWidth-1:0] pop_data,

    // Pop-side status flags
    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waivers.
    output logic bypass_ready,
    input logic bypass_valid_unstable,  // ri lint_check_waive INEFFECTIVE_NET
    input logic [BitWidth-1:0] bypass_data_unstable,  // ri lint_check_waive INEFFECTIVE_NET

    // RAM interface
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    // Port provided for clarity of interface design; only used for assertions.
    // ri lint_check_waive INEFFECTIVE_NET
    input  logic                 ram_rd_data_valid,
    input  logic [ BitWidth-1:0] ram_rd_data,

    // Internal handshakes between push and pop controllers
    input  logic ram_push,
    output logic ram_pop
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, BitWidth >= 1)

  `BR_ASSERT_INTG(ram_rd_latency_zero_a, ram_rd_addr_valid |-> ram_rd_data_valid)

  // Internal integration checks
  `BR_ASSERT_IMPL(bypass_unstable_c, !bypass_ready && bypass_valid_unstable)

  // This is not the tightest possible check, because we are planning to
  // support pipelined RAM access and CDC use cases that require supporting
  // delays between the push controller and pop controller.
  // The tightest possible check is slots == 0 |-> !ram_push.
  // This one is looser because items == Depth |-> slots == 0 (but the
  // converse is not true).
  `BR_ASSERT_IMPL(no_ram_push_when_all_items_a, items == Depth |-> !ram_push)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  logic pop;
  assign pop = pop_ready && pop_valid;

  // RAM path
  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_rd_addr (
      .clk,
      .rst,
      .incr_valid(ram_rd_addr_valid),
      .incr(1'b1),
      .value(ram_rd_addr),
      .value_next()  // unused
  );

  // Datapath
  assign ram_rd_addr_valid = ram_pop;
  if (EnableBypass) begin : gen_bypass
    assign bypass_ready = empty && pop_ready;
    assign pop_valid = !empty || bypass_valid_unstable;
    assign pop_data = empty ? bypass_data_unstable : ram_rd_data;
    assign ram_pop = pop && !bypass_valid_unstable;
  end else begin : gen_no_bypass
    assign bypass_ready = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
    assign pop_valid = !empty;
    assign pop_data = ram_rd_data;
    assign ram_pop = pop;
    br_misc_unused br_misc_unused_bypass_valid_unstable (.in(bypass_valid_unstable));
    br_misc_unused #(
        .BitWidth(BitWidth)
    ) br_misc_unused_bypass_data_unstable (
        .in(bypass_data_unstable)
    );
  end
  br_misc_unused br_misc_unused_ram_rd_data_valid (.in(ram_rd_data_valid));  // implied

  // Status flags
  assign items_next = ram_push && !ram_pop ? items + 1 : !ram_push && ram_pop ? items - 1 : items;
  assign empty_next = items_next == 0;

  `BR_REGL(items, items_next, ram_push || ram_pop)
  `BR_REGIL(empty, empty_next, ram_push || ram_pop, 1'b1)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(ram_rd_addr_in_range_a, ram_rd_addr_valid |-> ram_rd_addr < Depth)

  // Flow control and latency
  `BR_ASSERT_IMPL(pop_invalid_when_empty_a, empty |-> !pop_valid)
  `BR_ASSERT_IMPL(cutthrough_latency_1_cycle_a, empty && ram_push |=> !empty && pop_valid)
  `BR_ASSERT_IMPL(bypass_ready_only_when_empty_and_pop_ready_a, bypass_ready |-> empty && pop_ready)

  // RAM
  `BR_ASSERT_IMPL(ram_read_a, ram_pop |-> ram_rd_data_valid && ram_rd_data == pop_data)

  // Flags
  `BR_ASSERT_IMPL(items_in_range_a, items <= Depth)
  `BR_ASSERT_IMPL(items_next_a, ##1 items == $past(items_next))
  `BR_ASSERT_IMPL(push_and_pop_items_a, ram_push && ram_pop |-> items_next == items)
  `BR_ASSERT_IMPL(push_items_a, ram_push && !ram_pop |-> items_next == items + 1)
  `BR_ASSERT_IMPL(pop_items_a, !ram_push && ram_pop |-> items_next == items - 1)
  `BR_ASSERT_IMPL(empty_a, empty == (items == 0))

endmodule : br_fifo_pop_ctrl
