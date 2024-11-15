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
// Bedrock-RTL One-Hot Select Demultiplexer
//
// A 1-to-N demultiplexer with a one-hot select.
//
// The input is replicated to all outputs, but at most one output is valid;
// the selected output is determined by the one-hot encoded select input,
// and it is valid only when the input is also valid.
//
// When select == 0 then out_valid == '0 regardless of in_valid.

`include "br_asserts_internal.svh"

module br_demux_onehot #(
    // Number of outputs to distribute among. Must be >= 2.
    parameter int NumSymbolsOut = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth   = 1
) (
    // Onehot-encoded select. Must be in range of NumSymbolsOut.
    input  logic [NumSymbolsOut-1:0]                  select,
    input  logic                                      in_valid,
    input  logic [  SymbolWidth-1:0]                  in,
    // The selected out_valid bit is high when the corresponding in_valid is high.
    output logic [NumSymbolsOut-1:0]                  out_valid,
    output logic [NumSymbolsOut-1:0][SymbolWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_out_a, NumSymbolsOut >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  // TODO(mgottscho, #109):
  // ASSERT_COMB macro has an always_comb block that only has an
  // assertion inside. Need to add this waiver until we can figure out
  // how to handle it properly in the macro.
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_INTG(select_onehot0_a, $onehot0(select))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign out_valid = {NumSymbolsOut{in_valid}} & select;
  for (genvar i = 0; i < NumSymbolsOut; i++) begin : gen_outs
    assign out[i] = in;
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Ensure only one out_valid is high if in_valid is high
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(out_valid_onehot0_a, $onehot0(out_valid))
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(out_valid_a, (in_valid && $onehot(select)) == $onehot(out_valid))
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(out_invalid_when_select_0_a,
                       (out_valid == '0) || ((select != '0) && in_valid))

endmodule : br_demux_onehot
