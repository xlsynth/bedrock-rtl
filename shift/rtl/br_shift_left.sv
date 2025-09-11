// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_shift_left #(
    // The number of symbols to shift. Must be >=2.
    parameter int NumSymbols = 2,
    // The width of each symbol. Must be >=1.
    parameter int SymbolWidth = 1,
    // The maximum number of symbols to shift. Must be >=1 and < NumSymbols.
    parameter int MaxShift = 1,
    // The width of the shift amount.
    localparam int ShiftWidth = $clog2(MaxShift + 1)
) (
    input logic [NumSymbols-1:0][SymbolWidth-1:0] in,
    input logic [ShiftWidth-1:0] shift,
    input logic [SymbolWidth-1:0] fill,
    output logic out_valid,
    output logic [NumSymbols-1:0][SymbolWidth-1:0] out
);
  // Integration checks
  `BR_ASSERT_STATIC(legal_num_symbols_a, NumSymbols >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  `BR_ASSERT_STATIC(legal_max_shift_a, MaxShift >= 1 && MaxShift < NumSymbols)

  // Implementation

  logic [ShiftWidth:0][NumSymbols-1:0][SymbolWidth-1:0] stages;

  assign stages[0] = in;
  assign out = stages[ShiftWidth];

  for (genvar i = 0; i < ShiftWidth; i++) begin : gen_shift_right
    localparam int ShiftAmount = 1 << i;
    logic [NumSymbols-1:0][SymbolWidth-1:0] shifted_in;

    assign shifted_in  = {stages[i][NumSymbols-ShiftAmount-1:0], {ShiftAmount{fill}}};
    assign stages[i+1] = shift[i] ? shifted_in : stages[i];
  end

  // This might always be true if MaxShift is one less than a power of two.
  // ri lint_check_waive INVALID_COMPARE
  assign out_valid = shift <= MaxShift;

  // Implementation checks

  // TODO(zhemao): Decide what assertions we want to add here.

endmodule
