// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Binary Select Multiplexer with Structured Gates
//
// An N-to-1 multiplexer with a binary select.
//
// The out signal is set to in[i] for which select == i.
// Select must be in range of NumSymbolsIn.
//
// Manually builds a tree of mux2 gates instead of relying on
// the synthesis tool. This may be necessary if implementing an
// asynchronous path. If you don't need structured gates (almost
// always the case), use br_mux_bin instead.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_mux_bin_structured_gates #(
    // Number of inputs to select among. Must be >= 1.
    parameter  int NumSymbolsIn = 1,
    // The width of each symbol in bits. Must be >= 1.
    parameter  int SymbolWidth  = 1,
    localparam int SelectWidth  = br_math::clamped_clog2(NumSymbolsIn)
) (
    // ri lint_check_waive FANOUT_LIMIT
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

  if (NumSymbolsIn == 1) begin : gen_base
    `BR_UNUSED(select);
    assign out = in;
    assign out_valid = select == 1'b0;

  end else begin : gen_n

    // Round up number of input symbols to a power of 2, padding with 0s.
    // When select is out of range, the output will be 0, which matches the behavior of br_mux_bin.
    localparam int PaddedNumSymbolsIn = 2 ** $clog2(NumSymbolsIn);
    localparam int NumLevels = $clog2(PaddedNumSymbolsIn);

    // The final output is computed through a tree of mux2 gates.
    // The number of stages is clog2(NumSymbolsIn).
    // This signal contains the intermediate results of each stage.
    // Stage 0 is the input and stage NumLevels is the output.
    logic [NumLevels:0][PaddedNumSymbolsIn-1:0][SymbolWidth-1:0] in_stages;

    always_comb begin
      in_stages[0] = '0;  // ri lint_check_waive OVERWRITTEN
      in_stages[0][NumSymbolsIn-1:0] = in;
    end

    for (genvar i = 0; i < NumLevels; i++) begin : gen_level
      // At each stage, each mux2 will cover 2x the number of input
      // symbols as the previous stage.
      localparam int LastStageNumSymbolsInPerMux = 2 ** i;
      localparam int LastStageNumSymbols = br_math::ceil_div(
          PaddedNumSymbolsIn, LastStageNumSymbolsInPerMux
      );
      localparam int NumSymbolsInPerMux = 2 ** (i + 1);
      localparam int NumMuxes = br_math::ceil_div(PaddedNumSymbolsIn, NumSymbolsInPerMux);

      for (genvar j = 0; j < NumMuxes; j++) begin : gen_mux
        // Each output of the stage depends on two inputs from the previous stage.
        for (genvar k = 0; k < SymbolWidth; k++) begin : gen_mux2_gate
          br_gate_mux2 br_gate_mux2_inst (
              .sel(select[i]),
              .in0(in_stages[i][(j*2)+0][k]),
              .in1(in_stages[i][(j*2)+1][k]),
              .out(in_stages[i+1][j][k])
          );
        end
      end

      // Tie-off unused upper part of this stage's output.
      assign in_stages[i+1][PaddedNumSymbolsIn-1:NumMuxes] = '0;
      // Mark as unread the unused upper part of this stage's input.
      if (i != 0) begin : gen_last_stage_unused
        `BR_UNUSED_NAMED(last_stage_unused, in_stages[i][PaddedNumSymbolsIn-1:LastStageNumSymbols])
      end
    end

    assign out = in_stages[NumLevels][0];
    `BR_UNUSED_NAMED(final_stage_unused, in_stages[NumLevels][PaddedNumSymbolsIn-1:1])

    assign out_valid = select < NumSymbolsIn;  // ri lint_check_waive INVALID_COMPARE
  end

endmodule : br_mux_bin_structured_gates
