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
    assign out = in;
    assign out_valid = select == 1'b0;

  end else begin : gen_n

    localparam int NumLevels = $clog2(NumSymbolsIn);

    // The final output is computed through a tree of mux2 gates.
    // The number of stages is clog2(NumSymbolsIn).
    // This signal contains the intermediate results of each stage.
    // Stage 0 is the input and stage NumLevels is the output.
    logic [NumLevels:0][NumSymbolsIn-1:0][SymbolWidth-1:0] in_stages;

    assign in_stages[0] = in;

    // Build a tree of muxes with select taking successive bits
    // starting from the LSB. Each time, the distance between
    // inputs of the mux2s double. So stage 0 (the input), pairs
    // 0&1, 2&3, 4&5, etc. Stage 1 pairs 0&2, 4&6, 8&10, etc. and so on.
    // For non power-of-2 NumSymbolsIn, any pairing that goes outside the range
    // will have the missing input replaced with zero to match the behavior
    // of the non-structured br_mux_bin.
    for (genvar i = 0; i < NumLevels; i++) begin : gen_level
      localparam int InputStride = 2 ** i;
      localparam int OutputStride = 2 * InputStride;
      localparam int NumMuxes = br_math::ceil_div(NumSymbolsIn, OutputStride);

      for (genvar j = 0; j < NumMuxes; j++) begin : gen_mux
        localparam int In0Index = j * OutputStride;
        localparam int In1Index = j * OutputStride + InputStride;
        localparam int OutIndex = In0Index;
        localparam int OutZeroLsb = OutIndex + 1;
        localparam int OutZeroMsb = br_math::min2(OutIndex + OutputStride - 1, NumSymbolsIn - 1);
        localparam int In0UnusedLsb = In0Index + 1;
        localparam int In0UnusedMsb = br_math::min2(In0Index + InputStride - 1, NumSymbolsIn - 1);
        localparam int In1UnusedLsb = In1Index + 1;
        localparam int In1UnusedMsb = br_math::min2(In1Index + InputStride - 1, NumSymbolsIn - 1);

        logic [SymbolWidth-1:0] stage_in0, stage_in1, stage_out;

        assign stage_in0 = in_stages[i][In0Index];

        if (In1Index < NumSymbolsIn) begin : gen_in1
          assign stage_in1 = in_stages[i][In1Index];
        end else begin : gen_in1_tieoff
          assign stage_in1 = '0;
        end

        // Each output of the stage depends on two inputs from the previous stage.
        for (genvar k = 0; k < SymbolWidth; k++) begin : gen_mux2_gate
          br_gate_mux2 br_gate_mux2_inst (
              .sel(select[i]),
              .in0(stage_in0[k]),
              .in1(stage_in1[k]),
              .out(stage_out[k])
          );
        end


        assign in_stages[i+1][OutIndex] = stage_out;
        if (OutZeroLsb <= OutZeroMsb) begin : gen_out_zero
          assign in_stages[i+1][OutZeroMsb:OutZeroLsb] = '0;
        end

        // Mark as unread the previous stage values in between the input strides
        if (In0UnusedLsb <= In0UnusedMsb) begin : gen_in0_unused
          `BR_UNUSED_NAMED(last_stage_unused0, in_stages[i][In0UnusedMsb:In0UnusedLsb])
        end
        if (In1UnusedLsb <= In1UnusedMsb) begin : gen_in1_unused
          `BR_UNUSED_NAMED(last_stage_unused1, in_stages[i][In1UnusedMsb:In1UnusedLsb])
        end
      end
    end

    assign out = in_stages[NumLevels][0];
    `BR_UNUSED_NAMED(final_stage_unused, in_stages[NumLevels][NumSymbolsIn-1:1])

    assign out_valid = select < NumSymbolsIn;  // ri lint_check_waive INVALID_COMPARE
  end

endmodule : br_mux_bin_structured_gates
