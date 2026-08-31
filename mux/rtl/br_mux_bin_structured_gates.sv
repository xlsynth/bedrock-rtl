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
`include "br_assign.svh"
`include "br_unused.svh"

module br_mux_bin_structured_gates #(
    // Number of inputs to select among. Must be >= 1.
    parameter int NumSymbolsIn = 1,
    // The number of inputs to each mux gate. Currently only 2 and 4 are supported.
    parameter int GateRadix = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth = 1,
    localparam int SelectWidth = br_math::clamped_clog2(NumSymbolsIn)
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
  `BR_ASSERT_STATIC(gate_radix_supported_a, (GateRadix == 2) || (GateRadix == 4))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  if (NumSymbolsIn == 1) begin : gen_base
    assign out = in;
    assign out_valid = select == 1'b0;

  end else begin : gen_n

    // Num levels is ceil(logN(NumSymbolsIn)) where N is the radix.
    localparam int NumLevels = br_math::clogb(GateRadix, NumSymbolsIn);
    // Need to pad the select if GateRadix > 2
    localparam int PaddedSelectWidth = NumLevels * $clog2(GateRadix);

    // The final output is computed through a tree of muxN gates.
    // This signal contains the intermediate results of each stage.
    // Stage 0 is the input and stage NumLevels is the output.
    logic [NumLevels:0][NumSymbolsIn-1:0][SymbolWidth-1:0] in_stages;
    logic [PaddedSelectWidth-1:0] select_padded;

    assign in_stages[0] = in;
    `BR_ASSIGN_MAYBE_ZERO_EXT(select_padded, select_padded, select)

    // Build a tree of muxes with select taking successive bits
    // starting from the LSB. Each time, the distance between
    // inputs of the mux gates is multiped by the gate radix.
    // For example, if GateRadix=2, stage 0 (the input), pairs 0&1, 2&3, 4&5,
    // etc. Stage 1 pairs 0&2, 4&6, 8&10, etc. and so on. For NumSymbolsIn that
    // are not powers of the gate radix, any pairing that goes outside the range
    // will have the missing input replaced with zero to match the behavior of
    // the non-structured br_mux_bin.
    for (genvar i = 0; i < NumLevels; i++) begin : gen_level
      localparam int InputStride = GateRadix ** i;
      localparam int OutputStride = GateRadix * InputStride;
      localparam int NumMuxes = br_math::ceil_div(NumSymbolsIn, OutputStride);

      for (genvar j = 0; j < NumMuxes; j++) begin : gen_mux
        localparam int OutIndex = j * OutputStride;
        localparam int OutZeroLsb = OutIndex + 1;
        localparam int OutZeroMsb = br_math::min2(OutIndex + OutputStride - 1, NumSymbolsIn - 1);

        logic [GateRadix-1:0][SymbolWidth-1:0] stage_in;
        logic [SymbolWidth-1:0] stage_out;

        for (genvar k = 0; k < GateRadix; k++) begin : gen_mux_inputs
          localparam int InIndex = j * OutputStride + k * InputStride;
          localparam int InUnusedLsb = InIndex + 1;
          localparam int InUnusedMsb = br_math::min2(InIndex + InputStride - 1, NumSymbolsIn - 1);

          if (InIndex < NumSymbolsIn) begin : gen_in
            assign stage_in[k] = in_stages[i][InIndex];
          end else begin : gen_in_tieoff
            assign stage_in[k] = '0;
          end

          if (InUnusedLsb <= InUnusedMsb) begin : gen_in_unused
            `BR_UNUSED_NAMED(prev_stage_unused, in_stages[i][InUnusedMsb:InUnusedLsb])
          end
        end

        // Each output of the stage depends on two inputs from the previous stage.
        for (genvar k = 0; k < SymbolWidth; k++) begin : gen_mux2_gate
          if (GateRadix == 2) begin : gen_mux2
            br_gate_mux2 br_gate_mux2_inst (
                .sel(select_padded[i]),
                .in0(stage_in[0][k]),
                .in1(stage_in[1][k]),
                .out(stage_out[k])
            );
          end else if (GateRadix == 4) begin : gen_mux4
            br_gate_mux4 br_gate_mux4_inst (
                .sel(select_padded[i*2+:2]),
                .in0(stage_in[0][k]),
                .in1(stage_in[1][k]),
                .in2(stage_in[2][k]),
                .in3(stage_in[3][k]),
                .out(stage_out[k])
            );
          end
        end

        assign in_stages[i+1][OutIndex] = stage_out;
        if (OutZeroLsb <= OutZeroMsb) begin : gen_out_zero
          assign in_stages[i+1][OutZeroMsb:OutZeroLsb] = '0;
        end
      end
    end

    assign out = in_stages[NumLevels][0];
    `BR_UNUSED_NAMED(final_stage_unused, in_stages[NumLevels][NumSymbolsIn-1:1])

    assign out_valid = select < NumSymbolsIn;  // ri lint_check_waive INVALID_COMPARE
  end

endmodule : br_mux_bin_structured_gates
