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
`include "br_unused.svh"

module br_fifo_pop_ctrl #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    parameter int RamReadLatency = 0,
    parameter bit RegisterPopOutputs = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Pop-side status flags
    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waivers.
    output logic bypass_ready,
    input logic bypass_valid_unstable,  // ri lint_check_waive INEFFECTIVE_NET
    input logic [Width-1:0] bypass_data_unstable,  // ri lint_check_waive INEFFECTIVE_NET

    // RAM interface
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    // Not used except for assertions in some configurations.
    // ri lint_check_waive INEFFECTIVE_NET
    input  logic                 ram_rd_data_valid,
    input  logic [    Width-1:0] ram_rd_data,

    // Internal handshakes between push and pop controllers
    input  logic push_beat,
    output logic pop_beat
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  `BR_ASSERT_INTG(ram_rd_latency_matches_a,
                  ram_rd_addr_valid |-> ##RamReadLatency ram_rd_data_valid)

  // Internal integration checks
  `BR_COVER_IMPL(bypass_unstable_c, !bypass_ready && bypass_valid_unstable)

  // This is not the tightest possible check, because we are planning to
  // support pipelined RAM access and CDC use cases that require supporting
  // delays between the push controller and pop controller.
  // The tightest possible check is slots == 0 |-> !push_beat.
  // This one is looser because items == Depth |-> slots == 0 (but the
  // converse is not true).
  `BR_ASSERT_IMPL(no_push_beat_when_all_items_a, items == Depth |-> !push_beat)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Core flow-control logic

  br_fifo_pop_ctrl_core #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RamReadLatency(RamReadLatency),
      .RegisterPopOutputs(RegisterPopOutputs)
  ) br_fifo_pop_ctrl_core (
      .clk,
      .rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .bypass_ready,  // ri lint_check_waive CONST_OUTPUT
      .bypass_valid_unstable,
      .bypass_data_unstable,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data,
      .empty,
      .items,
      .pop_beat
  );

  // Status flags
  br_counter #(
      .MaxValue(Depth)
  ) br_counter_items (
      .clk,
      .rst,

      .reinit       (1'b0),
      .initial_value('0),    // ri lint_check_waive UNSIZED_PORT_CONST

      .incr_valid(push_beat),
      .incr      (1'b1),

      .decr_valid(pop_beat),
      .decr      (1'b1),

      .value     (items),
      .value_next(items_next)
  );
  assign empty_next = items_next == 0;
  `BR_REGLI(empty, empty_next, push_beat || pop_beat, 1'b1)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(ram_rd_addr_in_range_a, ram_rd_addr_valid |-> ram_rd_addr < Depth)

  // Flow control and latency
  if (EnableBypass) begin : gen_bypass_cut_through_latency_check
    // If a RAM read is inflight when the bypass occurs, pop_valid will not
    // be asserted until the RAM read completes. So the range of the latency
    // from bypass to the input of the final register stage is
    // 0 to RamReadLatency.
    `BR_ASSERT_IMPL(bypass_cut_through_latency_a,
                    (bypass_valid_unstable && bypass_ready)
                    |->
                    ##[RegisterPopOutputs:RegisterPopOutputs+RamReadLatency] pop_valid)
  end
  `BR_ASSERT_IMPL(
      non_bypass_cut_through_latency_a,
      (push_beat && !bypass_ready) |-> ##(1+RamReadLatency+RegisterPopOutputs) pop_valid)

  localparam bit ZeroCutThroughLatency =
      !RegisterPopOutputs && (EnableBypass || (RamReadLatency == 0));

  if (ZeroCutThroughLatency) begin : gen_zero_lat_impl_checks
    `BR_COVER_IMPL(pop_valid_when_empty_c, pop_valid && empty)
  end else begin : gen_non_zero_lat_impl_checks
    `BR_ASSERT_IMPL(no_pop_valid_on_empty_a, pop_valid |-> !empty)
  end

  // Flags
  `BR_ASSERT_IMPL(items_in_range_a, items <= Depth)
  `BR_ASSERT_IMPL(push_and_pop_items_a, push_beat && pop_beat |-> items_next == items)
  `BR_ASSERT_IMPL(push_items_a, push_beat && !pop_beat |-> items_next == items + 1)
  `BR_ASSERT_IMPL(pop_items_a, !push_beat && pop_beat |-> items_next == items - 1)
  `BR_ASSERT_IMPL(empty_a, empty == (items == 0))

endmodule : br_fifo_pop_ctrl
