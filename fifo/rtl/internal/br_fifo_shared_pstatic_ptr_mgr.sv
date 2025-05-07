// Copyright 2025 The Bedrock-RTL Authors
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
//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Pointer Manager
//
// This module maintains the head (read pointer) address for each virtual FIFO
// and also computes the full, empty, and item counts.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pstatic_ptr_mgr #(
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, ram_items comes from counter registers
    // If 0, it is reconstructed from the head/tail pointers
    parameter bit RegisterRamItems = 0,

    localparam int AddrWidth  = br_math::clamped_clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Base/bound/size configuration
    input logic [NumFifos-1:0][ AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][ AddrWidth-1:0] config_bound,
    input logic [NumFifos-1:0][CountWidth-1:0] config_size,

    // Write pointer from push controller
    input logic [NumFifos-1:0] advance_tail,
    input logic [NumFifos-1:0][AddrWidth-1:0] tail_next,
    input logic [NumFifos-1:0][AddrWidth-1:0] tail,
    output logic [NumFifos-1:0] push_full,

    // Read pointer to pop controller
    input logic [NumFifos-1:0] head_ready,
    output logic [NumFifos-1:0] head_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] head,

    // Empty/item count to pop controller
    output logic [NumFifos-1:0] ram_empty,
    output logic [NumFifos-1:0][CountWidth-1:0] ram_items
);

  // Integration Assertions

  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_intg_checks
    `BR_ASSERT_IMPL(tail_updates_on_advance_a, advance_tail[i] |=> tail[i] == $past(tail_next[i]))
    `BR_ASSERT_IMPL(tail_stable_on_no_advance_a, !advance_tail[i] |=> tail[i] == $past(tail[i]))
  end

  // Implementation
  logic [NumFifos-1:0] advance_head;
  logic [NumFifos-1:0] reinit_head;
  logic [NumFifos-1:0][AddrWidth-1:0] head_next;
  logic [NumFifos-1:0] push_full_next;
  logic [NumFifos-1:0] ram_empty_next;

  assign advance_head = head_ready & head_valid;
  assign head_valid   = ~ram_empty;

  `BR_REG(push_full, push_full_next)
  `BR_REGI(ram_empty, ram_empty_next, {NumFifos{1'b1}})

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_pointers
    assign reinit_head[i] = advance_head[i] && (head[i] == config_bound[i]);

    br_counter_incr #(
        .MaxValue(Depth - 1),
        .MaxIncrement(1),
        .EnableReinitAndIncr(0),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_counter_incr_head (
        .clk,
        .rst,
        .reinit(reinit_head[i]),
        .initial_value(config_base[i]),
        .incr_valid(advance_head[i]),
        .incr(1'b1),
        .value(head[i]),
        .value_next(head_next[i])
    );

    always_comb begin
      if (advance_head[i] == advance_tail[i]) begin
        push_full_next[i] = push_full[i];
        ram_empty_next[i] = ram_empty[i];
      end else if (advance_head[i]) begin
        // If the head is advancing without the tail,
        // full must be false and empty may be true
        // if the head catches up to the tail.
        push_full_next[i] = 1'b0;
        ram_empty_next[i] = (head_next[i] == tail[i]);
      end else begin
        // If the tail is advancing without the head,
        // full may be true if the tail catches up to the head
        // and empty must be false.
        push_full_next[i] = (tail_next[i] == head[i]);
        ram_empty_next[i] = 1'b0;
      end
    end
  end

  if (RegisterRamItems) begin : gen_register_ram_items
    for (genvar i = 0; i < NumFifos; i++) begin : gen_ram_items
      br_counter #(
          .MaxValue(Depth),
          .EnableWrap(0),
          .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
      ) br_counter_ram_items (
          .clk,
          .rst,
          .reinit(1'b0),
          .initial_value('0),
          .incr_valid(advance_tail[i]),
          .incr(1'b1),
          .decr_valid(advance_head[i]),
          .decr(1'b1),
          .value_next(),
          .value(ram_items[i])
      );
    end
    `BR_UNUSED(config_size)
  end else begin : gen_reconstruct_ram_items
    for (genvar i = 0; i < NumFifos; i++) begin : gen_ram_items
      logic [AddrWidth-1:0] tail_head_diff;
      logic [AddrWidth-1:0] head_tail_diff;

      // If tail is greater than head, this is the number of items in the FIFO.
      assign tail_head_diff = tail[i] - head[i];
      // If head is greater than tail, this is the number of empty slots in the
      // FIFO.
      assign head_tail_diff = head[i] - tail[i];

      assign ram_items[i] =
          push_full[i] ? config_size[i] :
          (tail[i] >= head[i]) ? CountWidth'(tail_head_diff) :
          (config_size[i] - CountWidth'(head_tail_diff));
    end
  end

  // Implementation Assertions
  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_impl_checks
    `BR_ASSERT_IMPL(ram_empty_means_no_items_a, ram_empty[i] |-> (ram_items[i] == 0))
    `BR_ASSERT_IMPL(ram_empty_on_ptr_match_a, ram_empty[i] |-> (head[i] == tail[i]))
    `BR_ASSERT_IMPL(push_full_on_ptr_match_a, push_full[i] |-> (head[i] == tail[i]))
    `BR_ASSERT_IMPL(dual_advance_ram_items_stable_a,
                    (advance_head[i] && advance_tail[i]) |=> $stable(ram_items[i]))
    `BR_ASSERT_IMPL(
        head_advance_ram_items_decr_a,
        (advance_head[i] && !advance_tail[i]) |=> (ram_items[i] == $past(ram_items[i]) - 1))
    `BR_ASSERT_IMPL(
        tail_advance_ram_items_incr_a,
        (advance_tail[i] && !advance_head[i]) |=> (ram_items[i] == $past(ram_items[i]) + 1))
    `BR_ASSERT_IMPL(no_ram_items_overflow_a, ram_items[i] <= config_size[i])
  end

endmodule
