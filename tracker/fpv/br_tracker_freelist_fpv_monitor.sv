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

// Bedrock-RTL Free List Manager FPV checker

`include "br_asserts.svh"
`include "br_fv.svh"

module br_tracker_freelist_fpv_monitor #(
    // Number of entries in the freelist. Must be greater than NumAllocPerCycle.
    parameter int NumEntries = 2,
    // Number of allocations per cycle. Must be at least 1.
    parameter int NumAllocPerCycle = 1,
    // Number of deallocation ports. Must be at least 1.
    parameter int NumDeallocPorts = 1,
    // If 1, then register the alloc_sendable and alloc_entry_id outputs,
    // improving timing at the cost of an additional cycle of cut-through latency.
    // Note that if this is set to 0, the alloc_entry_id may be unstable
    parameter bit RegisterAllocOutputs = 1,
    // If 1, bypass deallocated entries to allocated entries.
    parameter bit EnableBypass = 0,
    // Cut-through latency of the tracker.
    localparam int CutThroughLatency = RegisterAllocOutputs + (EnableBypass ? 0 : 1),
    // The delay between an entry being deallocated and when the deallocation
    // is indicated by dealloc_count.
    // If dealloc_count is being used to manage credit returns, this must be set
    // so that allocation is not attemped until (CutThroughLatency - DeallocCountDelay) cycles
    // after deallocation is indicated on dealloc_count,
    // where CutThroughLatency = RegisterAllocOutputs + (EnableBypass ? 0 : 1).
    // Must be >= 0 and <= CutThroughLatency.
    parameter int DeallocCountDelay = CutThroughLatency,
    // If 1, then assert there are no dealloc_valid bits asserted at the end of the test.
    // It is expected that alloc_valid could be 1 at end of the test because it's
    // a natural idle condition for this design.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int EntryIdWidth = $clog2(NumEntries),
    localparam int DeallocCountWidth = $clog2(NumDeallocPorts + 1),
    localparam int AllocCountWidth = $clog2(NumAllocPerCycle + 1)
) (
    input logic                                           clk,
    input logic                                           rst,
    // Allocation Interface
    input logic [  AllocCountWidth-1:0]                   alloc_receivable,
    input logic [  AllocCountWidth-1:0]                   alloc_sendable,
    input logic [ NumAllocPerCycle-1:0][EntryIdWidth-1:0] alloc_entry_id,
    // Deallocation Interface
    input logic [  NumDeallocPorts-1:0]                   dealloc_valid,
    input logic [  NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id,
    // Number of deallocations that have been performed.
    // This count will be nonzero to indicate that a given number of
    // entries will be available for allocation again.
    input logic [DeallocCountWidth-1:0]                   dealloc_count
);

  // ----------FV modeling code----------
  // pick a random index for assertion
  logic [AllocCountWidth-1:0] fv_idx;
  `BR_ASSUME(fv_idx_a, $stable(fv_idx) && fv_idx < NumAllocPerCycle)

  logic alloc_extra_left;
  logic [AllocCountWidth-1:0] fv_allocated;
  logic [NumAllocPerCycle-1:0] fv_alloc_valid;

  logic [NumEntries-1:0] fv_entry_alloc;
  logic [NumEntries-1:0] fv_entry_dealloc;
  logic [NumEntries-1:0] fv_entry_used;

  assign alloc_extra_left = alloc_sendable > alloc_receivable;
  assign fv_allocated = alloc_extra_left ? alloc_receivable : alloc_sendable;

  // if fv_alloc_valid[i]=1, alloc_entry_id[i] is actually allocated this cycle
  always_comb begin
    fv_alloc_valid = 'd0;
    for (int i = 0; i < NumAllocPerCycle; i++) begin
      if (i < fv_allocated) begin
        fv_alloc_valid[i] = 1'd1;
      end
    end
  end

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumDeallocPorts; n++) begin : gen_asm
    `BR_ASSUME(dealloc_range_a, dealloc_valid[n] |-> dealloc_entry_id[n] < NumEntries)
    `BR_ASSUME(legal_dealloc_a, dealloc_valid[n] |-> fv_entry_used[dealloc_entry_id[n]])
  end

  // entry is being de-allocated this cycle
  always_comb begin
    fv_entry_dealloc = 'd0;
    for (int i = 0; i < NumDeallocPorts; i++) begin
      `BR_ASSUME(unique_dealloc_entry_id_a,
                 dealloc_valid[i] |-> !fv_entry_dealloc[dealloc_entry_id[i]])
      if (dealloc_valid[i]) begin
        fv_entry_dealloc[dealloc_entry_id[i]] = 1'd1;
      end
    end
  end

  // ----------FV assertions----------
  // entry is being allocated this cycle
  always_comb begin
    fv_entry_alloc = 'd0;
    for (int i = 0; i < NumAllocPerCycle; i++) begin
      `BR_ASSERT(unique_alloc_entry_id_a, fv_alloc_valid[i] |-> !fv_entry_alloc[alloc_entry_id[i]])
      if (fv_alloc_valid[i]) begin
        fv_entry_alloc[alloc_entry_id[i]] = 1'd1;
      end
    end
  end

  // entry is in progress: allocated not yet deallocated
  always_ff @(posedge clk) begin
    if (rst) begin
      fv_entry_used <= '0;
    end else begin
      for (int j = 0; j < NumDeallocPorts; j++) begin
        if (dealloc_valid[j]) begin
          fv_entry_used[dealloc_entry_id[j]] <= 1'd0;
        end
      end
      for (int i = 0; i < NumAllocPerCycle; i++) begin
        if (fv_alloc_valid[i]) begin
          fv_entry_used[alloc_entry_id[i]] <= 1'd1;
        end
      end
    end
  end

  // verilog_lint: waive-start line-length
  // Once an entry is allocated, the same entry cannot be allocated again until it is deallocated.
  if (EnableBypass) begin : gen_bypass
    `BR_ASSERT(no_entry_reuse_a,
               fv_alloc_valid[fv_idx] && !fv_entry_dealloc[alloc_entry_id[fv_idx]] |-> !fv_entry_used[alloc_entry_id[fv_idx]])
    // when freelist is empty, no more alloc_sendable
    `BR_ASSERT(freelist_empty_no_alloc_a,
               (fv_entry_used == {NumEntries{1'b1}}) && (fv_entry_dealloc == 'd0) |-> alloc_sendable == 'd0)
  end else begin : gen_non_bypass
    `BR_ASSERT(no_entry_reuse_a, fv_alloc_valid[fv_idx] |-> !fv_entry_used[alloc_entry_id[fv_idx]])
    // when freelist is empty, no more alloc_sendable
    `BR_ASSERT(freelist_empty_no_alloc_a,
               fv_entry_used == {NumEntries{1'b1}} |-> alloc_sendable == 'd0)
  end
  // verilog_lint: waive-stop line-length

  // if freelist is not empty, next cycle, some alloc_port should allocate another free entry
  `BR_ASSERT(forward_progress_a,
             (fv_entry_used | fv_entry_alloc) != {NumEntries{1'b1}} |=> alloc_sendable != 'd0)

  // Number of deallocations performed last cycle
  if (DeallocCountDelay == 0) begin : gen_latency0
    `BR_ASSERT(dealloc_count_a, dealloc_count == $countones(dealloc_valid))
  end else begin : gen_latency
    `BR_ASSERT(
        dealloc_count_a,
        ##DeallocCountDelay dealloc_count == $past($countones(dealloc_valid), DeallocCountDelay))
  end

  // ----------Critical Covers----------
  `BR_COVER(all_alloc_valid_c, &fv_alloc_valid)
  `BR_COVER(all_entry_used_c, &fv_entry_used)
  `BR_COVER(same_cyc_alloc_dealloc_c, (|fv_alloc_valid) && (|dealloc_valid))
  if (NumDeallocPorts <= NumEntries) begin : gen_cov
    `BR_COVER(all_dealloc_valid_c, &dealloc_valid)
  end

endmodule : br_tracker_freelist_fpv_monitor

bind br_tracker_freelist br_tracker_freelist_fpv_monitor #(
    .NumEntries(NumEntries),
    .NumAllocPerCycle(NumAllocPerCycle),
    .NumDeallocPorts(NumDeallocPorts),
    .RegisterAllocOutputs(RegisterAllocOutputs),
    .EnableBypass(EnableBypass),
    .DeallocCountDelay(DeallocCountDelay),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
