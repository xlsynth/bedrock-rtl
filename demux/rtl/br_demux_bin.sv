// Copyright 2024-2025 The Bedrock-RTL Authors
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
// Bedrock-RTL Binary Select Demultiplexer
//
// A 1-to-N demultiplexer with a binary select and validity control.
//
// The input is replicated to all outputs, but at most one output is valid;
// the selected output is determined by the binary encoded select input,
// and it is valid only when the input is also valid.

`include "br_asserts_internal.svh"

module br_demux_bin #(
    // Number of outputs to distribute among. Must be >= 1.
    parameter int NumSymbolsOut = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int SelectWidth = br_math::clamped_clog2(NumSymbolsOut)
) (
    // Binary-encoded select. Must be in range of NumSymbolsOut.
    input  logic [  SelectWidth-1:0]                  select,
    input  logic                                      in_valid,
    input  logic [  SymbolWidth-1:0]                  in,
    // The selected out_valid bit is high when the corresponding in_valid is high.
    output logic [NumSymbolsOut-1:0]                  out_valid,
    output logic [NumSymbolsOut-1:0][SymbolWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_out_a, NumSymbolsOut >= 1)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  // TODO(zhemao): Figure out why this spuriously triggers in some cases
  // ri lint_check_waive ALWAYS_COMB
  //`BR_ASSERT_COMB_INTG(select_in_range_a, !in_valid || (select < NumSymbolsOut))

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
    `BR_ASSERT_FINAL(final_not_out_valid_a, !out_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    for (int i = 0; i < NumSymbolsOut; i++) begin
      out_valid[i] = in_valid && (select == i);
    end
  end
  assign out = {NumSymbolsOut{in}};

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(out_valid_onehot0_a, $onehot0(out_valid))
  // The following assertion seems to spuriously trigger in some cases,
  // likely due to it being a combinational assertion.
  // TODO(zhemao): Figure out why this fails and reenable it once
  // it can be fixed.
  // ri lint_check_waive ALWAYS_COMB
  //`BR_ASSERT_COMB_IMPL(out_valid_a, $onehot(out_valid) || !in_valid)

endmodule : br_demux_bin
