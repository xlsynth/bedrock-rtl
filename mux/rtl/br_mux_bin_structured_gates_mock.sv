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
// Bedrock-RTL Binary Select Multiplexer with Structured Gates (MOCK version)
//
// An N-to-1 multiplexer with a binary select.
//
// The out signal is set to in[i] for which select == i.
// Select must be in range of NumSymbolsIn.
//
// Implementation wraps br_mux_bin, i.e., does not actually implement
// the structured gates. We need a duplicate/wrapper module because in simulation
// builds we want to use a mock version and in synthesis builds we want to use
// the real version, but the RTL parameterization must not be affected.
//
// For synthesis, make sure you include br_mux_bin_structured_gates.sv
// in the filelist instead of this file!!

`include "br_asserts.svh"

`ifdef SYNTHESIS
`BR_ASSERT_STATIC(do_not_synthesize_br_mux_bin_structured_gates_mock_a, 0)
`endif

// verilog_lint: waive-start module-filename
// ri lint_check_waive FILE_NAME
module br_mux_bin_structured_gates #(
    // Number of inputs to select among. Must be >= 2.
    parameter  int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth  = 1,
    localparam int SelectWidth  = $clog2(NumSymbolsIn)
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
  logic [SymbolWidth-1:0] out_internal;
  always_comb begin
    out_internal = '0;

    for (int i = 0; i < NumSymbolsIn; i++) begin
      out_internal |= ({SymbolWidth{select == i}} & in[i]);
    end
  end

  assign out_valid = select < NumSymbolsIn;  // ri lint_check_waive INVALID_COMPARE
  // This is terrible practice, but required to pass LEC against the synthesizable version
  // TODO(mgottscho): fix the synthesizable version and revert this manual X assignment
  // (switch implementation back to being a wrapper on br_mux_bin).
  // ri lint_check_waive X_USE
  assign out = out_valid ? out_internal : 'x;

endmodule : br_mux_bin_structured_gates

// verilog_lint: waive-stop module-filename
