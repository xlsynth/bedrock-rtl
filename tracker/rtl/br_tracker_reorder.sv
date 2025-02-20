// Issues tags on the allocate interface and receives tags on the
// dealloc_request interface. The tags are then put back into the original
// allocation order and returned on the dealloc_complete interface. Tags will
// not be re-used on the alloc interface before they are returned on the
// dealloc_complete interface.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder #(
    parameter int NumEntries = 2,
    parameter int EntryIdWidth = $clog2(NumEntries),
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1
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
    output logic [EntryIdWidth-1:0] dealloc_complete_entry_id
);

  // Integration Assertions
  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > 1)
  `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= $clog2(NumEntries))

  // Internal Counter Widths (in case narrower than EntryIdWidth)
  localparam int CounterValueWidth = $clog2(NumEntries);

  // Internal State
  logic [NumEntries-1:0] dealloc_pending;
  logic [NumEntries-1:0] dealloc_pending_next;

  `BR_REG(dealloc_pending, dealloc_pending_next)

  // Allocate Counter
  logic alloc_beat;
  logic [CounterValueWidth-1:0] alloc_counter_value;
  assign alloc_beat = alloc_valid && alloc_ready;

  br_counter_incr #(
      .MaxValue(NumEntries - 1),
      .MaxIncrement(1),
      .EnableSaturate(0),
      .EnableAssertFinalNotValid(0)
  ) allocate_counter (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(alloc_beat),
      .incr(1'b1),
      .value(alloc_counter_value),
      .value_next()
  );

  assign alloc_entry_id = EntryIdWidth'(alloc_counter_value);

  // Deallocate Counter
  logic dealloc_complete_beat;
  logic [CounterValueWidth-1:0] dealloc_complete_counter_value;
  assign dealloc_complete_beat = dealloc_complete_valid && dealloc_complete_ready;

  br_counter_incr #(
      .MaxValue(NumEntries - 1),
      .MaxIncrement(1),
      .EnableSaturate(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotDeallocValid)
  ) deallocate_counter (
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

  // Free Entry Counter
  localparam int FreeEntryCountWidth = $clog2(NumEntries + 1);
  logic [FreeEntryCountWidth-1:0] free_entry_count;
  br_counter #(
      .MaxValue(NumEntries),
      .MaxChange(1),
      .EnableWrap(0),
      .EnableSaturate(0)
  ) free_entry_counter (
      .clk,
      .rst,
      .reinit(1'b0),
      .initial_value(FreeEntryCountWidth'($unsigned(NumEntries))),
      .incr_valid(dealloc_complete_beat),
      .incr(1'b1),
      .decr_valid(alloc_beat),
      .decr(1'b1),
      .value(free_entry_count),
      .value_next()
  );

  logic free_entry_empty;
  assign free_entry_empty = (free_entry_count == 0);

  // Deallocate Pending Bitmap
  //
  // Deallocation requests must be completed in order. Requests pend inside of the
  // pending bitmap where they are visited in order according to the deallocation
  // counter (so they are released in order).

  for (genvar i = 0; i < NumEntries; i++) begin : gen_dealloc_pending_next
    logic set_dealloc_pending;
    logic clear_dealloc_pending;

    assign set_dealloc_pending   = dealloc_valid && (dealloc_entry_id == i);
    assign clear_dealloc_pending = dealloc_complete_beat && (dealloc_complete_entry_id == i);
    `BR_ASSERT(no_reuse_before_complete_a, $onehot0({set_dealloc_pending, clear_dealloc_pending}))

    assign dealloc_pending_next[i] = clear_dealloc_pending ? 1'b0 :
                                         set_dealloc_pending ? 1'b1 :
                                         dealloc_pending[i];
  end

  // Dealloc Complete Logic
  `BR_ASSERT(valid_dealloc_entry_id_a, dealloc_valid |-> (dealloc_entry_id < NumEntries))
  assign dealloc_complete_valid = dealloc_pending[dealloc_entry_id[CounterValueWidth-1:0]];
  if ($clog2(NumEntries) < EntryIdWidth) begin : gen_unused_upper_addr_assert
    `BR_ASSERT(unused_upper_addr_a, dealloc_entry_id[EntryIdWidth-1:CounterValueWidth] == '0)
  end

  // Allocate Logic
  assign alloc_valid = !free_entry_empty;

endmodule
