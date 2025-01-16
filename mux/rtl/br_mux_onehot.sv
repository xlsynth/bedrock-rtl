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
// Bedrock-RTL onehot select multiplexer
//
// An N-to-1 multiplexer with a onehot select.
//
// The out signal will be set to in[i] for which select[i] is 1.
// The select must have at most one bit set.

`include "br_asserts_internal.svh"

module br_mux_onehot #(
    // Number of inputs to select among. Must be >= 2.
    parameter int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth  = 1
) (
    input  logic [NumSymbolsIn-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_INTG(select_onehot0_a, $onehot0(select))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    out = '0;

    for (int i = 0; i < NumSymbolsIn; i++) begin
      out |= ({SymbolWidth{select[i]}} & in[i]);
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

endmodule : br_mux_onehot
