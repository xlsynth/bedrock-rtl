// Copyright 2024-2025 The Bedrock-RTL Authors
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

// Basic FPV checks for all FIFO variations

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_basic_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit EnableBypass = 1,
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic                  full,
    input logic                  full_next,
    input logic [CountWidth-1:0] slots,
    input logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    input logic                  empty,
    input logic                  empty_next,
    input logic [CountWidth-1:0] items,
    input logic [CountWidth-1:0] items_next
);

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))

  // ----------FV Modeling Code----------
  logic [CountWidth-1:0] fv_items;
  logic [CountWidth-1:0] fv_slots;

  `BR_REG(fv_items, fv_items + (push_valid & push_ready) - (pop_valid & pop_ready))
  assign fv_slots = Depth - fv_items;

  // ----------Sanity Check----------
  if (EnableBypass) begin : gen_bypass
    `BR_ASSERT(no_pop_when_empty_a, empty && !push_valid |-> !pop_valid)
  end else begin : gen_non_bypass
    `BR_ASSERT(no_pop_when_empty_a, empty |-> !pop_valid)
  end

  // empty, full check
  `BR_ASSERT(full_a, (fv_items == Depth) == full)
  `BR_ASSERT(empty_a, (fv_items == 'd0) == empty)

  // primary output and its next check
  `BR_ASSERT(full_next_a, $fell(rst) |=> full == $past(full_next))
  `BR_ASSERT(slots_next_a, $fell(rst) |=> slots == $past(slots_next))
  `BR_ASSERT(empty_next_a, $fell(rst) |=> empty == $past(empty_next))
  `BR_ASSERT(items_next_a, $fell(rst) |=> items == $past(items_next))

  // slots, items check
  `BR_ASSERT(items_a, fv_items == items)
  `BR_ASSERT(slots_a, fv_slots == slots)

  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(Depth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid & push_ready),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid & pop_ready),
      .outgoing_data(pop_data)
  );

  // ----------Forward Progress Check----------
  `BR_ASSERT(no_deadlock_pop_a, push_valid |-> s_eventually pop_valid)

  // ----------Critical Covers----------
  `BR_COVER(fifo_full_c, full)

endmodule : br_fifo_basic_fpv_monitor
