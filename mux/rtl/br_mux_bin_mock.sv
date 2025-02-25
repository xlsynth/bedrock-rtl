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
// Bedrock-RTL Binary Select Multiplexer (Mock Behavioral Version)
//
// An N-to-1 multiplexer with a binary select.
//
// The out signal is set to in[i] for which select == i.
// Select must be in range of NumSymbolsIn.
//
// This module is a mock behavioral model and must not be used for synthesis,
// because the UseStructuredGates parameter is ignored.

`include "br_asserts_internal.svh"

`ifdef SYNTHESIS
`BR_ASSERT_STATIC(do_not_synthesize_br_gate_mux_bin_mock_a, 0)
`endif

// verilog_lint: waive-start module-filename
// ri lint_check_waive FILE_NAME
module br_mux_bin #(
    // Number of inputs to select among. Must be >= 2.
    parameter int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth = 1,
    // If set to 1, manually build a tree of mux2 gates instead of relying on
    // the synthesis tool.  This may be necessary if implementing an
    // asynchronous path.
    // NOTE: Parameter is ignored -- it is only provided for instance
    // interchangability with br_mux_bin.sv.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit UseStructuredGates = 0,
    localparam int SelectWidth = $clog2(NumSymbolsIn)
) (
    input  logic [ SelectWidth-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out,
    output logic                                     out_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
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

// verilog_lint: waive-stop module-filename
