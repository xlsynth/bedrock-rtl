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
    // Port provided for clarity of interface design; only used for assertions.
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

  // Flow control
  assign pop_beat = pop_ready && pop_valid;

  // RAM path
  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_rd_addr (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(AddrWidth'(1'b0)),
      .incr_valid(ram_rd_addr_valid),
      .incr(1'b1),
      .value(ram_rd_addr),
      .value_next()  // unused
  );

  // Datapath
  if (RamReadLatency == 0) begin : gen_zero_rd_lat
    logic             internal_pop_valid;
    logic             internal_pop_ready;
    logic [Width-1:0] internal_pop_data;
    logic             internal_empty;

    if (EnableBypass) begin : gen_bypass
      assign bypass_ready = internal_empty && internal_pop_ready;
      assign internal_pop_valid = !internal_empty || bypass_valid_unstable;
      assign internal_pop_data = internal_empty ? bypass_data_unstable : ram_rd_data;
      assign ram_rd_addr_valid = internal_pop_valid && internal_pop_ready && !internal_empty;
    end else begin : gen_no_bypass
      // TODO(zhemao, #157): Replace this with BR_TIEOFF macros once they are fixed
      assign bypass_ready = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
      assign internal_pop_valid = !internal_empty;
      assign internal_pop_data = ram_rd_data;
      assign ram_rd_addr_valid = internal_pop_valid && internal_pop_ready;

      `BR_UNUSED_NAMED(bypass_signals, {bypass_valid_unstable, bypass_data_unstable})
    end
    `BR_UNUSED(ram_rd_data_valid)  // implied

    if (RegisterPopOutputs) begin : gen_reg_pop
      br_flow_reg_fwd #(
          .Width(Width)
      ) br_flow_reg_fwd_pop (
          .clk,
          .rst,
          .push_valid(internal_pop_valid),
          .push_ready(internal_pop_ready),
          .push_data (internal_pop_data),
          .pop_valid,
          .pop_ready,
          .pop_data
      );
      // internal_empty is true if there are no items or if there is one item
      // and it is already in the staging register
      assign internal_empty = empty || ((items == 1'b1) && pop_valid);
    end else begin : gen_noreg_pop
      assign internal_empty = empty;
      assign pop_valid = internal_pop_valid;
      assign pop_data = internal_pop_data;
      assign internal_pop_ready = pop_ready;
    end
  end else begin : gen_nonzero_rd_lat
    br_fifo_staging_buffer #(
        .EnableBypass      (EnableBypass),
        .TotalDepth        (Depth),
        .RamReadLatency    (RamReadLatency),
        .Width             (Width),
        .RegisterPopOutputs(RegisterPopOutputs)
    ) br_fifo_staging_buffer (
        .clk,
        .rst,

        // If bypass is disabled, bypass_ready will be driven by constant
        // TODO(zhemao, #157): Remove this once lint waiver issue is fixed
        .bypass_ready,  // ri lint_check_waive CONST_OUTPUT
        .bypass_valid_unstable,
        .bypass_data_unstable,

        .total_items(items),

        .ram_rd_addr_valid,
        .ram_rd_data_valid,
        .ram_rd_data,

        .pop_ready,
        .pop_valid,
        .pop_data
    );
  end

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
  `BR_REGIL(empty, empty_next, push_beat || pop_beat, 1'b1)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(ram_rd_addr_in_range_a, ram_rd_addr_valid |-> ram_rd_addr < Depth)

  // Flow control and latency
  if (EnableBypass) begin : gen_bypass_cut_through_latency_check
    `BR_ASSERT_IMPL(bypass_cut_through_latency_a,
                    (bypass_valid_unstable && bypass_ready) |-> ##(RegisterPopOutputs) pop_valid)
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
