// SPDX-License-Identifier: Apache-2.0

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
    // Number of inputs to select among. Must be >= 1.
    parameter  int NumSymbolsIn = 1,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth  = 1,
    localparam int SelectWidth  = br_math::clamped_clog2(NumSymbolsIn)
) (
    input  logic [ SelectWidth-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out,
    output logic                                     out_valid
);

  br_mux_bin #(
      .NumSymbolsIn(NumSymbolsIn),
      .SymbolWidth (SymbolWidth)
  ) br_mux_bin (
      .select,
      .in,
      .out,
      .out_valid
  );

endmodule : br_mux_bin_structured_gates

// verilog_lint: waive-stop module-filename
