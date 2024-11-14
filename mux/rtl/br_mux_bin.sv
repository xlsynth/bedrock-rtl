// Copyright 2024 The Bedrock-RTL Authors
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
// Bedrock-RTL Binary Select Multiplexer
//
// An N-to-1 multiplexer with a binary select.
//
// The out signal is set to in[i] for which select == i.
// Select must be in range of NumSymbolsIn.

`include "br_asserts_internal.svh"

module br_mux_bin #(
    // Number of inputs to select among. Must be >= 2.
    parameter  int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth  = 1,
    localparam int SelectWidth  = $clog2(NumSymbolsIn)
) (
    input  logic [ SelectWidth-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  // TODO(mgottscho, #109):
  // ASSERT_COMB macro has an always_comb block that only has an
  // assertion inside. Need to add this waiver until we can figure out
  // how to handle it properly in the macro.
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_INTG(select_in_range_a, $isunknown(select) || select < NumSymbolsIn)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    out = '0;

    for (int i = 0; i < NumSymbolsIn; i++) begin
      out |= ({SymbolWidth{select == i}} & in[i]);
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

endmodule : br_mux_bin
