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

// Bedrock-RTL Reorder with buffer basic FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_buffer_basic_fpv_monitor #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = 1,
    // Width of the data payload.
    parameter int DataWidth = 1,
    // Number of clock cycles for the RAM read latency.
    parameter int RamReadLatency = 1,
    localparam int EntryCountWidth = $clog2(NumEntries + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    input logic alloc_valid,
    input logic [EntryIdWidth-1:0] alloc_entry_id,

    // Unordered Response Interface
    input logic unordered_resp_push_valid,
    input logic [EntryIdWidth-1:0] unordered_resp_push_entry_id,
    input logic [DataWidth-1:0] unordered_resp_push_data,

    // Unordered Response Interface
    input logic reordered_resp_pop_ready,
    input logic reordered_resp_pop_valid,
    input logic [DataWidth-1:0] reordered_resp_pop_data,

    // Count Information
    input logic [EntryCountWidth-1:0] free_entry_count,
    input logic [EntryCountWidth-1:0] allocated_entry_count
);

  // ----------FV modeling code----------
  localparam int EntryWidth = $clog2(NumEntries);
  logic [NumEntries-1:0] fv_entry_allocated;
  logic [NumEntries-1:0] fv_entry_allocated_nxt;
  logic [EntryIdWidth-1:0] fv_reordered_resp_entry_id;
  logic fv_fifo_empty;
  logic fv_fifo_full;

  // Entry allocated not yet deallocated
  always_comb begin
    fv_entry_allocated_nxt = fv_entry_allocated;
    if (alloc_valid & alloc_ready) begin
      fv_entry_allocated_nxt[alloc_entry_id] = 1'b1;
    end
    if (unordered_resp_push_valid) begin
      fv_entry_allocated_nxt[unordered_resp_push_entry_id] = 1'b0;
    end
  end

  `BR_REG(fv_entry_allocated, fv_entry_allocated_nxt)

  // alloc and reordered_resp_pop are in order
  fv_fifo #(
      .Depth(NumEntries * 2 + RamReadLatency),
      .DataWidth(EntryIdWidth),
      .Bypass(0)
  ) entry_id_fifo (
      .clk(clk),
      .rst(rst),
      .push(alloc_valid & alloc_ready),
      .push_data(alloc_entry_id),
      .pop(reordered_resp_pop_valid & reordered_resp_pop_ready),
      .pop_data(fv_reordered_resp_entry_id),
      .empty(fv_fifo_empty),
      .full(fv_fifo_full)
  );

  // ----------FV assumptions----------
  `BR_ASSUME(dealloc_range_a,
             unordered_resp_push_valid |-> unordered_resp_push_entry_id < NumEntries)
  `BR_ASSUME(legal_dealloc_a,
             unordered_resp_push_valid |-> fv_entry_allocated[unordered_resp_push_entry_id])
  if (EntryIdWidth > EntryWidth) begin : gen_asm
    `BR_ASSUME(legal_alloc_entry_id_a, alloc_entry_id[EntryIdWidth-1:EntryWidth] == '0)
    `BR_ASSUME(legal_unordered_resp_push_entry_id_a,
               unordered_resp_push_entry_id[EntryIdWidth-1:EntryWidth] == '0)
  end

  // ----------FV assertions----------
  `BR_ASSERT(alloc_valid_ready_a, alloc_valid && !alloc_ready |=> alloc_valid && $stable
                                  (alloc_entry_id))
  `BR_ASSERT(
      reordered_resp_data_stable_a,
      reordered_resp_pop_valid && !reordered_resp_pop_ready |=> reordered_resp_pop_valid && $stable
      (reordered_resp_pop_data))
  `BR_ASSERT(no_entry_reuse_a, alloc_valid |-> !fv_entry_allocated[alloc_entry_id])

  `BR_ASSERT(entry_full_no_alloc_a, fv_entry_allocated == {NumEntries{1'b1}} |-> !alloc_valid)

  `BR_ASSERT(allocated_entry_count_a, $countones(fv_entry_allocated) == allocated_entry_count)
  `BR_ASSERT(free_entry_count_a, (NumEntries - allocated_entry_count) == free_entry_count)

  // pick random entry to check data integrity and ordering
  logic [EntryIdWidth-1:0] fv_entry_id;
  logic fv_unordered_request_valid;
  logic fv_reordered_resp_valid;

  `BR_ASSUME(fv_entry_id_a, $stable(fv_entry_id) && fv_entry_id < NumEntries)
  assign fv_unordered_request_valid = unordered_resp_push_valid &&
                                    (unordered_resp_push_entry_id == fv_entry_id);
  assign fv_reordered_resp_valid = reordered_resp_pop_valid & reordered_resp_pop_ready &&
                                     (fv_reordered_resp_entry_id == fv_entry_id);

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(DataWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumEntries + RamReadLatency)
  ) data_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_unordered_request_valid),
      .incoming_data(unordered_resp_push_data),
      .outgoing_vld(fv_reordered_resp_valid),
      .outgoing_data(reordered_resp_pop_data)
  );

endmodule
