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
    // Number of entries in the freelist. Must be greater than 2 X NumAllocPorts.
    parameter int NumEntries = 2,
    // Number of allocation ports. Must be at least 1.
    parameter int NumAllocPorts = 1,
    // Number of deallocation ports. Must be at least 1.
    parameter int NumDeallocPorts = 1,
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int EntryIdWidth = $clog2(NumEntries)
) (
    input logic                                         clk,
    input logic                                         rst,
    // Allocation Interface
    input logic [  NumAllocPorts-1:0]                   alloc_ready,
    input logic [  NumAllocPorts-1:0]                   alloc_valid,
    input logic [  NumAllocPorts-1:0][EntryIdWidth-1:0] alloc_entry_id,
    // Deallocation Interface
    input logic [NumDeallocPorts-1:0]                   dealloc_valid,
    input logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id
);

  // pick random alloc port for assertions
  localparam int PortWidth = NumAllocPorts == 1 ? 1 : $clog2(NumAllocPorts);
  logic [PortWidth-1:0] fv_alloc_port;
  `BR_ASSUME(fv_alloc_port_a, $stable(fv_alloc_port) && fv_alloc_port < NumAllocPorts)

  logic [NumEntries-1:0] fv_entry_alloc;
  logic [NumEntries-1:0] fv_entry_dealloc;
  logic [NumEntries-1:0] fv_entry_used;

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumDeallocPorts; n++) begin : gen_asm
    `BR_ASSUME(dealloc_range_a, dealloc_valid[n] |-> dealloc_entry_id[n] < NumEntries)
    `BR_ASSUME(legal_dealloc_a, dealloc_valid[n] |-> fv_entry_used[dealloc_entry_id[n]])
  end

  // entry is being de-allocated this cycle
  always_comb begin
    fv_entry_dealloc = 'd0;
    for (int i = 0; i < NumDeallocPorts; i++) begin
      `BR_ASSUME(uniqie_dealloc_entry_id_a,
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
    for (int i = 0; i < NumAllocPorts; i++) begin
      `BR_ASSERT(uniqie_alloc_entry_id_a, alloc_valid[i] |-> !fv_entry_alloc[alloc_entry_id[i]])
      if (alloc_valid[i]) begin
        fv_entry_alloc[alloc_entry_id[i]] = 1'd1;
      end
    end
  end

  // entry is in progress: allocated not yet deallocated
  always_ff @(posedge clk) begin
    if (rst) begin
      fv_entry_used <= '0;
    end else begin
      for (int i = 0; i < NumAllocPorts; i++) begin
        if (alloc_valid[i] && alloc_ready[i]) begin
          fv_entry_used[alloc_entry_id[i]] <= 1'd1;
        end
      end
      for (int j = 0; j < NumDeallocPorts; j++) begin
        if (dealloc_valid[j]) begin
          fv_entry_used[dealloc_entry_id[j]] <= 1'd0;
        end
      end
    end
  end

  // verilog_lint: waive-start line-length
  // if alloc is not accepted by alloc_ready, alloc_entry_id should be stable
  `BR_ASSERT(
      alloc_valid_ready_a,
      alloc_valid[fv_alloc_port] && !alloc_ready[fv_alloc_port] |=> alloc_valid[fv_alloc_port] && $stable
      (alloc_entry_id[fv_alloc_port]))

  // Once an entry is allocated, the same entry cannot be allocated again until it is deallocated.
  `BR_ASSERT(
      no_entry_reuse_a,
      alloc_valid[fv_alloc_port] && alloc_ready[fv_alloc_port] |-> !fv_entry_used[alloc_entry_id[fv_alloc_port]])

  // when freelist is empty, no more alloc_valid
  `BR_ASSERT(freelist_empty_no_alloc_a, fv_entry_used == {NumEntries{1'b1}} |-> alloc_valid == 'd0)

  // if freelist is not empty, next cycle, some alloc_port should allocate another free entry
  `BR_ASSERT(forward_progress_a,
             (fv_entry_used | fv_entry_alloc) != {NumEntries{1'b1}} |=> alloc_valid != 'd0)
  // verilog_lint: waive-stop line-length

  // ----------Critical Covers----------
  `BR_COVER(all_alloc_valid_c, &alloc_valid)
  `BR_COVER(all_entry_used_c, &fv_entry_used)
  `BR_COVER(same_cyc_alloc_dealloc_c, (|alloc_valid) && (|dealloc_valid))
  if (NumDeallocPorts <= NumEntries) begin : gen_cov
    `BR_COVER(all_dealloc_valid_c, &dealloc_valid)
  end

endmodule : br_tracker_freelist_fpv_monitor

bind br_tracker_freelist br_tracker_freelist_fpv_monitor #(
    .NumEntries(NumEntries),
    .NumAllocPorts(NumAllocPorts),
    .NumDeallocPorts(NumDeallocPorts)
) monitor (.*);
