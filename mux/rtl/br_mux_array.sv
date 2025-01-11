// Copyright 2025 The Bedrock-RTL Authors
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
// Bedrock-RTL Multiplexer Array
//
// An array of N-to-1 multiplexers with a select.
//
// The out[j] signal is set to in[i] for which select == i.
// Select must be in range of NumSymbolsIn.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_mux_array #(
    // Number of inputs to select among. Must be >= 2.
    parameter  int NumSymbolsIn  = 2,
    // Number of outputs to select among. Must be >= 1.
    parameter  int NumSymbolsOut = 1,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth   = 1,
    localparam int SelectWidth   = $clog2(NumSymbolsIn)
) (
    input  logic [NumSymbolsOut-1:0][SelectWidth-1:0] select,
    input  logic [ NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [NumSymbolsOut-1:0][SymbolWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
  `BR_ASSERT_STATIC(legal_num_symbols_out_a, NumSymbolsOut >= 1)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)

  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_INTG(select_in_range_a, $isunknown(select) || select < NumSymbolsIn)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  generate
    for (genvar i = 0; i < NumSymbolsOut; i++) begin : gen_mux
      br_mux_bin #(
          .NumSymbolsIn(NumSymbolsIn),
          .SymbolWidth (SymbolWidth)
      ) br_mux_bin (
          .select(select[i]),
          .in(in),
          .out(out[i])
      );
    end
  endgenerate


endmodule : br_mux_array
