// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_mux_bin #(
    // Number of inputs to select among. Must be >= 1.
    parameter  int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth  = 1,
    localparam int SelectWidth  = br_math::clamped_clog2(NumSymbolsIn)
) (
    input  logic [ SelectWidth-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out,
    output logic                                     out_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 1)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    out = '0;

    for (int i = 0; i < NumSymbolsIn; i++) begin
      out |= ({SymbolWidth{select == i}} & in[i]);
    end
  end

  assign out_valid = select < NumSymbolsIn;  // ri lint_check_waive INVALID_COMPARE

endmodule : br_mux_bin
