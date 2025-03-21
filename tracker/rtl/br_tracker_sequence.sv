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
//
// Bedrock-RTL Sequence Number Tracker
//
// Allocates sequence numbers in counting order, up to MaxAllocSize per cycle.
// Min(alloc_receivable, alloc_sendable) sequence numbers are allocated on a clock
// cycle and output on the alloc_entry_id interface. When MaxAllocSize is 1,
// sendable/receivable is equivalent to valid/ready.
//
// Sequence numbers are freed in the allocation order via the dealloc
// interface (up to MaxAllocSize per cycle). Because the numbers must be freed
// in the allocation order, the actual sequence number need not be returned on
// the dealloc interface, only the number of sequence numbers to return.

`include "br_asserts.svh"
`include "br_asserts_internal.svh"

module br_tracker_sequence #(
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
    output logic [MaxAllocSizeWidth-1:0] alloc_sendable,
    output logic [MaxAllocSize-1:0][EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input logic dealloc_valid,
    input logic [MaxAllocSizeWidth-1:0] dealloc_size,

    // Count Information
    output logic [EntryCountWidth-1:0] free_entry_count,
    output logic [EntryCountWidth-1:0] allocated_entry_count
);

  // Internal Counter Widths (in case narrower than EntryIdWidth)
  localparam int AllocCounterValueWidth = $clog2(NumEntries);

  // Work around limitation of br_counter_incr where MaxAllocSize must be less than NumEntries
  localparam int MaxIncrementAllocCounter = (MaxAllocSize == NumEntries) ? MaxAllocSize - 1 : MaxAllocSize;
  localparam int AllocCounterIncrWidth = $clog2(MaxIncrementAllocCounter+1);

  // Variable Declarations
  logic alloc_beat;
  logic [AllocCounterValueWidth-1:0] alloc_counter_value;
  logic [MaxAllocSizeWidth-1:0] alloc_size;
  assign alloc_beat = (alloc_receivable > 0) && (alloc_sendable > 0);
  assign alloc_size = (alloc_receivable > alloc_sendable) ? alloc_sendable : alloc_receivable;

  // Integration Assertions
  `BR_ASSERT_STATIC(alloc_size_lte_num_entries_a, MaxAllocSize <= NumEntries)
  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > 1)
  `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= $clog2(NumEntries))
  `BR_ASSERT_INTG(dealloc_size_lte_used_seqno_a,
                  dealloc_valid |-> (dealloc_size <= allocated_entry_count))
  `BR_ASSERT_INTG(dealloc_size_gt_zero_a, dealloc_valid |-> (dealloc_size > 0))
  `BR_ASSERT_INTG(dealloc_size_lte_max_alloc_size_a,
                  dealloc_valid |-> (dealloc_size <= MaxAllocSize))
  if (EnableAssertFinalNotDeallocValid) begin : gen_assert_final_not_dealloc_valid
    `BR_ASSERT_FINAL(final_not_dealloc_valid_a, !dealloc_valid)
  end

  // Allocate Counter

  // the br_counter_incr doesn't support an incr amount that is greater than MaxValue,
  // so we need to squash the increment if it's equal to NumEntries. This is functionally
  // correct because NumEntries % NumEntries == 0, so the increment is equivalent to 0.
  logic alloc_beat_squash_wrap;
  if (MaxAllocSize == NumEntries) begin : gen_alloc_beat_squash_wrap
    assign alloc_beat_squash_wrap = alloc_beat && (alloc_size != NumEntries);
  end else begin : gen_alloc_beat_squash_wrap_false
    assign alloc_beat_squash_wrap = alloc_beat;
  end

  br_counter_incr #(
      .MaxValue(NumEntries - 1),
      .MaxIncrement(MaxIncrementAllocCounter),
      .EnableSaturate(0),
      .EnableAssertFinalNotValid(0)
  ) br_counter_incr_allocate_counter (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(alloc_beat_squash_wrap),
      .incr(AllocCounterIncrWidth'(alloc_size)),
      .value(alloc_counter_value),
      .value_next()
  );

  // Generate Entry ID Outputs
  assign alloc_entry_id[0] = EntryIdWidth'(alloc_counter_value);

  localparam int NextValueWidth = $clog2(NumEntries + MaxAllocSize);
  for (genvar i = 1; i < MaxAllocSize; i++) begin : gen_alloc_entry_id
    logic [NextValueWidth-1:0] next_value;
    logic [NextValueWidth-1:0] next_value_wrapped;
    // ri lint_check_waive ARITH_EXTENSION
    assign next_value = alloc_counter_value[0] + i;
    assign next_value_wrapped = (next_value >= NumEntries) ? (next_value - NumEntries) : next_value;
    assign alloc_entry_id[i] = EntryIdWidth'(next_value_wrapped);
  end

  // Free Entry Counter

  br_counter #(
      .MaxValue(NumEntries),
      .MaxChange(MaxAllocSize),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) br_counter_free_entry_counter (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value(EntryCountWidth'($unsigned(NumEntries))),
      .incr_valid(dealloc_valid),
      .incr(dealloc_size),
      .decr_valid(alloc_beat),
      .decr(alloc_size),
      .value(free_entry_count),
      .value_next()
  );

  assign allocated_entry_count = EntryCountWidth'($unsigned(NumEntries)) - free_entry_count;

  assign alloc_sendable = (free_entry_count > MaxAllocSize ? MaxAllocSize
                                    : MaxAllocSizeWidth'(free_entry_count));

endmodule
