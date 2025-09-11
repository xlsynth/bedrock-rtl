// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_sequence_fpv_monitor #(
    // Number of sequence numbers that can be allocated.
    parameter int NumEntries = 2,
    // Maximum number of sequence numbers that can be allocated/deallocated in a single beat.
    parameter int MaxAllocSize = 1,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = $clog2(NumEntries),
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int MaxAllocSizeWidth = $clog2(MaxAllocSize + 1),
    localparam int EntryCountWidth = $clog2(NumEntries + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic [MaxAllocSizeWidth-1:0] alloc_receivable,
    input logic [MaxAllocSizeWidth-1:0] alloc_sendable,
    input logic [MaxAllocSize-1:0][EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input logic dealloc_valid,
    input logic [MaxAllocSizeWidth-1:0] dealloc_size,

    // Count Information
    input logic [EntryCountWidth-1:0] free_entry_count,
    input logic [EntryCountWidth-1:0] allocated_entry_count
);

  // ----------FV modeling code----------
  function automatic logic [EntryIdWidth-1:0] wrap(input logic [EntryIdWidth-1:0] base,
                                                   input logic [MaxAllocSizeWidth-1:0] incr,
                                                   input int MaxValue);
    logic [EntryIdWidth:0] base_pad;
    base_pad = {1'b0, base};
    wrap = base_pad + incr >= MaxValue ? base + incr - MaxValue : base + incr;
    return wrap;
  endfunction

  localparam int EntryWidth = $clog2(NumEntries);
  logic alloc_extra_left;
  logic [MaxAllocSizeWidth-1:0] fv_allocated;

  logic [MaxAllocSize-1:0] fv_alloc_valid;
  logic [MaxAllocSize-1:0] fv_dealloc_valid;
  logic [EntryIdWidth-1:0] cur_dealloc_entry_id;
  logic [MaxAllocSize-1:0][EntryIdWidth-1:0] fv_dealloc_entry_id;

  logic [NumEntries-1:0] fv_entry_allocated;
  logic [NumEntries-1:0] fv_entry_allocated_nxt;

  assign alloc_extra_left = alloc_sendable > alloc_receivable;
  assign fv_allocated = alloc_extra_left ? alloc_receivable : alloc_sendable;

  // if fv_alloc_valid[i]=1, alloc_entry_id[i] is actually allocated this cycle
  always_comb begin
    fv_alloc_valid = 'd0;
    for (int i = 0; i < MaxAllocSize; i++) begin
      if (i < fv_allocated) begin
        fv_alloc_valid[i] = 1'd1;
      end
    end
  end

  // verilog_lint: waive-start line-length
  // if fv_dealloc_valid[i]=1, dealloc_entry_id[i] is actually deallocated this cycle
  always_comb begin
    fv_dealloc_valid = 'd0;
    fv_dealloc_entry_id = 'd0;
    // dealloc size > 0
    if (dealloc_valid) begin
      fv_dealloc_valid[0] = 'd1;
      fv_dealloc_entry_id[0] = cur_dealloc_entry_id;
      for (int i = 1; i < MaxAllocSize; i++) begin
        if (i < dealloc_size) begin
          fv_dealloc_valid[i] = 1'd1;
          fv_dealloc_entry_id[i] = wrap(fv_dealloc_entry_id[i-1], 'd1, NumEntries);
        end
      end
    end
  end
  // verilog_lint: waive-stop line-length

  `BR_REGL(cur_dealloc_entry_id, wrap(cur_dealloc_entry_id, dealloc_size, NumEntries),
           dealloc_valid)

  // Entry allocated not yet deallocated
  always_comb begin
    fv_entry_allocated_nxt = fv_entry_allocated;
    for (int i = 0; i < MaxAllocSize; i++) begin
      `BR_ASSERT(no_deplicated_entry_a,
                 fv_alloc_valid[i] |-> !fv_entry_allocated_nxt[alloc_entry_id[i]])
      if (fv_alloc_valid[i]) begin
        fv_entry_allocated_nxt[alloc_entry_id[i]] = 1'b1;
      end
      if (fv_dealloc_valid[i]) begin
        fv_entry_allocated_nxt[fv_dealloc_entry_id[i]] = 1'b0;
      end
    end
  end

  `BR_REG(fv_entry_allocated, fv_entry_allocated_nxt)

  // ----------FV assumptions----------
  `BR_ASSUME(alloc_receivable_range_a, alloc_receivable <= MaxAllocSize)
  `BR_ASSUME(dealloc_size_range_a, (dealloc_size != 'd0) && (dealloc_size <= MaxAllocSize))
  `BR_ASSUME(legal_dealloc_size_a, dealloc_valid |-> dealloc_size <= $countones(fv_entry_allocated))

  // ----------FV assertions----------
  `BR_ASSERT(alloc_sendable_increment_a, alloc_extra_left |=> alloc_sendable >= $past
                                         (alloc_sendable - alloc_receivable))
  for (genvar i = 0; i < MaxAllocSize; i++) begin : gen_ast
    `BR_ASSERT(no_entry_reuse_a, fv_alloc_valid[i] |-> !fv_entry_allocated[alloc_entry_id[i]])
  end

  `BR_ASSERT(allocated_entry_count_a, $countones(fv_entry_allocated) == allocated_entry_count)
  `BR_ASSERT(free_entry_count_a, (NumEntries - allocated_entry_count) == free_entry_count)

endmodule : br_tracker_sequence_fpv_monitor

bind br_tracker_sequence br_tracker_sequence_fpv_monitor #(
    .NumEntries(NumEntries),
    .MaxAllocSize(MaxAllocSize),
    .EntryIdWidth(EntryIdWidth),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
