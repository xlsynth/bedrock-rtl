// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder #(
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
    output logic alloc_valid,
    output logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic dealloc_valid,
    input logic [EntryIdWidth-1:0] dealloc_entry_id,

    // Deallocation Complete Interface
    input logic dealloc_complete_ready,
    output logic dealloc_complete_valid,
    output logic [EntryIdWidth-1:0] dealloc_complete_entry_id,

    // Count Information
    output logic [EntryCountWidth-1:0] free_entry_count,
    output logic [EntryCountWidth-1:0] allocated_entry_count
);

  // Deallocation Pending Bitmap
  // Used in integration checks
  logic [NumEntries-1:0] dealloc_pending;

  // Integration Assertions
  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > 1)
  `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= $clog2(NumEntries))
  `BR_ASSERT_INTG(valid_dealloc_entry_id_a, dealloc_valid |-> (dealloc_entry_id < NumEntries))
  `BR_ASSERT_INTG(dealloc_entry_is_pending_a,
                  dealloc_complete_valid |-> dealloc_pending[dealloc_complete_entry_id])

  logic [NumEntries-1:0] dealloc_pending_next;

  // Internal Counter Widths (in case narrower than EntryIdWidth)
  localparam int CounterValueWidth = $clog2(NumEntries);

  // Sequence Number Tracker
  logic dealloc_complete_beat;
  assign dealloc_complete_beat = dealloc_complete_valid && dealloc_complete_ready;

  br_tracker_sequence #(
      .NumEntries(NumEntries),
      .MaxAllocSize(1),
      .EntryIdWidth(EntryIdWidth),
      .EnableAssertFinalNotDeallocValid(0)
  ) br_tracker_sequence_allocate_counter (
      .clk,
      .rst,
      //
      .alloc_receivable(alloc_ready),
      .alloc_sendable(alloc_valid),
      .alloc_entry_id,
      //
      .dealloc_valid(dealloc_complete_beat),
      .dealloc_size(1'b1),
      //
      .free_entry_count,
      .allocated_entry_count
  );

  // Deallocate Counter
  logic [CounterValueWidth-1:0] dealloc_complete_counter_value;

  br_counter_incr #(
      .MaxValue(NumEntries - 1),
      .MaxIncrement(1),
      .EnableSaturate(0),
      .EnableCoverZeroIncrement(0),
      .EnableCoverReinit(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotDeallocValid)
  ) br_counter_incr_deallocate_counter (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(dealloc_complete_beat),
      .incr(1'b1),
      .value(dealloc_complete_counter_value),
      .value_next()
  );

  assign dealloc_complete_entry_id = EntryIdWidth'(dealloc_complete_counter_value);

  // Deallocate Pending Bitmap
  //
  // Deallocation requests must be completed in order. Requests pend inside of the
  // pending bitmap where they are visited in order according to the deallocation
  // counter (so they are released in order).

  `BR_REGL(dealloc_pending, dealloc_pending_next, (dealloc_valid || dealloc_complete_beat))

  for (genvar i = 0; i < NumEntries; i++) begin : gen_dealloc_pending_next
    logic set_dealloc_pending;
    logic clear_dealloc_pending;

    assign set_dealloc_pending = dealloc_valid && (dealloc_entry_id == i);
    assign clear_dealloc_pending = dealloc_complete_beat && (dealloc_complete_entry_id == i);

    assign dealloc_pending_next[i] = set_dealloc_pending ? 1'b1 :
                              clear_dealloc_pending ? 1'b0 :
                              dealloc_pending[i];

  end

  // Dealloc Complete Logic
  assign dealloc_complete_valid = dealloc_pending[dealloc_complete_counter_value];

  // Implementation Assertions
  if ($clog2(NumEntries) < EntryIdWidth) begin : gen_unused_upper_addr_assert
    `BR_ASSERT_IMPL(unused_upper_addr_a, dealloc_entry_id[EntryIdWidth-1:CounterValueWidth] == '0)
  end

  `BR_ASSERT_IMPL(
      no_request_and_complete_same_id_a,
      (dealloc_valid && dealloc_complete_beat) |-> (dealloc_entry_id != dealloc_complete_entry_id))

endmodule
