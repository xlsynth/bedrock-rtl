// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Multi-Transfer Register (Forward Variant)
//
// A buffer for multi-transfer flow-controlled interface that
// breaks the combinational path for sendable/data.
//
// The buffer holds up to NumSymbols data elements and can push and pop
// up to that many per cycle.
//
// The cut-through latency (minimum delay from push_sendable to pop_sendable) is 1 cycle.
// The backpressure latency (minimum delay from pop_receivable to push_receivable) is 0 cycles.
// The steady-state throughput is NumSymbols transactions per cycle.
//
// The number of symbols transferred in a given cycle is the minimum of sendable and receivable.
// If pop_sendable > pop_receivable on a cycle, pop_data is shifted down by pop_receivable slots
// and push_receivable will be (NumSymbols - pop_sendable + pop_receivable). The new data will
// fill in starting at (pop_sendable - pop_receivable).

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_multi_xfer_reg_fwd #(
    // The number of symbols that can be transferred in a single cycle.
    // Must be at least 2.
    parameter int NumSymbols = 2,
    // The width of a single symbol.
    // Must be at least 1.
    parameter int SymbolWidth = 1,
    // If 1, assert that push_data is stable when push_sendable > push_receivable.
    // If 0, cover that push_data is unstable when push_sendable > push_receivable.
    parameter bit EnableAssertPushDataStability = 1,
    // If 1, assert that the buffer is empty and push_sendable is 0
    // at end of simulation.
    parameter int EnableAssertFinalNotSendable = 1,

    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    input logic clk,
    input logic rst,

    output logic [CountWidth-1:0] push_receivable,
    input logic [CountWidth-1:0] push_sendable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] push_data,

    input logic [CountWidth-1:0] pop_receivable,
    output logic [CountWidth-1:0] pop_sendable,
    output logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data
);

  // Integration Assertions
  `BR_ASSERT_STATIC(legal_num_symbols_a, NumSymbols >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)

  br_multi_xfer_checks_sendable_data_intg #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .EnableAssertDataStability(EnableAssertPushDataStability)
  ) br_multi_xfer_checks_sendable_data_intg_push (
      .clk(clk),
      .rst(rst),
      .receivable(push_receivable),
      .sendable(push_sendable),
      .data(push_data)
  );

  if (EnableAssertFinalNotSendable) begin : gen_assert_final_not_sendable
    `BR_ASSERT_FINAL(final_push_not_sendable_a, push_sendable == '0)
    `BR_ASSERT_FINAL(final_pop_not_sendable_a, pop_sendable == '0)
  end

  // Implementation

  logic [CountWidth-1:0] pop_xfer_count;
  logic [CountWidth-1:0] pop_sendable_after_xfer;
  logic [CountWidth-1:0] push_xfer_count;
  logic [CountWidth-1:0] pop_sendable_next;
  logic [NumSymbols-1:0][SymbolWidth-1:0] push_data_qual;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data_next;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data_next_old;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data_next_old_qual;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data_next_new;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data_next_new_qual;
  logic pop_update;

  assign pop_xfer_count = (pop_sendable < pop_receivable) ? pop_sendable : pop_receivable;
  assign pop_sendable_after_xfer = pop_sendable - pop_xfer_count;

  assign push_receivable = NumSymbols - pop_sendable_after_xfer;
  assign push_xfer_count = (push_sendable < push_receivable) ? push_sendable : push_receivable;

  assign pop_sendable_next = pop_sendable_after_xfer + push_xfer_count;

  localparam int ShiftWidth = $clog2(NumSymbols);

  br_shift_right #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .MaxShift(NumSymbols - 1)
  ) br_shift_right_data (
      .in(pop_data),
      .fill('0),
      .shift(pop_xfer_count[ShiftWidth-1:0]),
      .out(pop_data_next_old),
      .out_valid()
  );

  // The shifter cannot perform a shift of NumSymbols, so we need to handle that case
  // separately. Shifting by NumSymbols is equivalent to clearing the output.
  assign pop_data_next_old_qual = (pop_xfer_count == NumSymbols) ? '0 : pop_data_next_old;

  // Qualify the push data so that only the sendable data is non-zero.
  // That allows us to just combine the old and new data using bitwise OR later.
  for (genvar i = 0; i < NumSymbols; i++) begin : gen_push_data_qual
    assign push_data_qual[i] = (push_sendable > i) ? push_data[i] : '0;
  end

  br_shift_left #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .MaxShift(NumSymbols - 1)
  ) br_shift_left_data (
      .in(push_data_qual),
      .fill('0),
      .shift(pop_sendable_after_xfer[ShiftWidth-1:0]),
      .out(pop_data_next_new),
      .out_valid()
  );

  // Handle the case where pop_sendable_after_xfer is NumSymbols.
  assign pop_data_next_new_qual = (pop_sendable_after_xfer == NumSymbols) ? '0 : pop_data_next_new;
  assign pop_data_next = pop_data_next_old_qual | pop_data_next_new_qual;
  assign pop_update = (|push_xfer_count) || (|pop_xfer_count);

  `BR_REGL(pop_sendable, pop_sendable_next, pop_update)
  `BR_REGL(pop_data, pop_data_next, pop_update)

  // Implementation Assertions
  br_multi_xfer_checks_sendable_data_impl #(
      .NumSymbols (NumSymbols),
      .SymbolWidth(SymbolWidth)
  ) br_multi_xfer_checks_sendable_data_impl_pop (
      .clk(clk),
      .rst(rst),
      .receivable(pop_receivable),
      .sendable(pop_sendable),
      .data(pop_data)
  );
endmodule
