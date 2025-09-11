// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_mux_bin_array #(
    // Number of inputs to select among. Must be >= 2.
    parameter  int NumSymbolsIn  = 2,
    // Number of outputs to select among. Must be >= 1.
    parameter  int NumSymbolsOut = 1,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth   = 1,
    localparam int SelectWidth   = $clog2(NumSymbolsIn)
) (
    input logic [NumSymbolsOut-1:0][SelectWidth-1:0] select,
    input logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [NumSymbolsOut-1:0][SymbolWidth-1:0] out,
    output logic [NumSymbolsOut-1:0] out_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
  `BR_ASSERT_STATIC(legal_num_symbols_out_a, NumSymbolsOut >= 1)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  for (genvar i = 0; i < NumSymbolsOut; i++) begin : gen_mux
    br_mux_bin #(
        .NumSymbolsIn(NumSymbolsIn),
        .SymbolWidth (SymbolWidth)
    ) br_mux_bin (
        .select(select[i]),
        .in(in),
        .out(out[i]),
        .out_valid(out_valid[i])
    );
  end

endmodule : br_mux_bin_array
