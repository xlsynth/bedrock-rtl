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

// Bedrock-RTL Reordering Tracker

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_fpv_monitor #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = $clog2(NumEntries),
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int EntryCountWidth = $clog2(NumEntries + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    input logic alloc_valid,
    input logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic dealloc_valid,
    input logic [EntryIdWidth-1:0] dealloc_entry_id,

    // Deallocation Complete Interface
    input logic dealloc_complete_ready,
    input logic dealloc_complete_valid,
    input logic [EntryIdWidth-1:0] dealloc_complete_entry_id,

    // Count Information
    input logic [EntryCountWidth-1:0] free_entry_count,
    input logic [EntryCountWidth-1:0] allocated_entry_count
);

  // ----------FV modeling code----------
  localparam int EntryWidth = $clog2(NumEntries);
  logic [NumEntries-1:0] fv_entry_allocated;
  logic [NumEntries-1:0] fv_entry_allocated_nxt;
  logic [NumEntries-1:0] fv_entry_used;
  logic [NumEntries-1:0] fv_entry_used_nxt;

  // Entry allocated not yet deallocated
  always_comb begin
    fv_entry_allocated_nxt = fv_entry_allocated;
    if (alloc_valid & alloc_ready) begin
      fv_entry_allocated_nxt[alloc_entry_id] = 1'b1;
    end
    if (dealloc_valid) begin
      fv_entry_allocated_nxt[dealloc_entry_id] = 1'b0;
    end
  end

  // Tags will not be re-used on the alloc interface,
  // before they are returned on the dealloc_complete interface.
  always_comb begin
    fv_entry_used_nxt = fv_entry_used;
    if (alloc_valid & alloc_ready) begin
      fv_entry_used_nxt[alloc_entry_id] = 1'b1;
    end
    if (dealloc_complete_valid & dealloc_complete_ready) begin
      fv_entry_used_nxt[dealloc_complete_entry_id] = 1'b0;
    end
  end

  `BR_REG(fv_entry_used, fv_entry_used_nxt)
  `BR_REG(fv_entry_allocated, fv_entry_allocated_nxt)

  // ----------FV assumptions----------
  `BR_ASSUME(dealloc_range_a, dealloc_valid |-> dealloc_entry_id < NumEntries)
  `BR_ASSUME(legal_dealloc_a, dealloc_valid |-> fv_entry_allocated[dealloc_entry_id])
  if (EntryIdWidth > EntryWidth) begin : gen_asm
    `BR_ASSUME(legal_alloc_entry_id_a, alloc_entry_id[EntryIdWidth-1:EntryWidth] == '0)
    `BR_ASSUME(legal_dealloc_entry_id_a, dealloc_entry_id[EntryIdWidth-1:EntryWidth] == '0)
  end

  // ----------FV assertions----------
  `BR_ASSERT(alloc_valid_ready_a, alloc_valid && !alloc_ready |=> alloc_valid && $stable
                                  (alloc_entry_id))
  `BR_ASSERT(dealloc_complete_valid_ready_a,
             dealloc_complete_valid && !dealloc_complete_ready |=> dealloc_complete_valid && $stable
             (dealloc_complete_entry_id))

  `BR_ASSERT(no_entry_reuse_a, alloc_valid |-> !fv_entry_used[alloc_entry_id])
  `BR_ASSERT(no_spurious_complete_a,
             dealloc_complete_valid |-> fv_entry_used[dealloc_complete_entry_id])
  `BR_ASSERT(dealloc_sanity_a, dealloc_valid |-> fv_entry_used[dealloc_entry_id])
  `BR_ASSERT(dealloc_complete_sanity_a,
             dealloc_complete_valid |-> !fv_entry_allocated[dealloc_complete_entry_id])

  `BR_ASSERT(entry_full_no_alloc_a, fv_entry_used == {NumEntries{1'b1}} |-> !alloc_valid)
  `BR_ASSERT(forward_progress_a, fv_entry_used_nxt != {NumEntries{1'b1}} |=> alloc_valid)

  `BR_ASSERT(allocated_entry_count_a, $countones(fv_entry_used) == allocated_entry_count)
  `BR_ASSERT(free_entry_count_a, (NumEntries - allocated_entry_count) == free_entry_count)

  // alloc and dealloc_complete are in order
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(EntryIdWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumEntries)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(alloc_valid & alloc_ready),
      .incoming_data(alloc_entry_id),
      .outgoing_vld(dealloc_complete_valid & dealloc_complete_ready),
      .outgoing_data(dealloc_complete_entry_id)
  );

  // ----------Critical Covers----------
  `BR_COVER(same_cyc_alloc_dealloc_c, alloc_valid & dealloc_valid)

endmodule : br_tracker_reorder_fpv_monitor

bind br_tracker_reorder br_tracker_reorder_fpv_monitor #(
    .NumEntries(NumEntries),
    .EntryIdWidth(EntryIdWidth),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
