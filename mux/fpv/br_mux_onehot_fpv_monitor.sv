// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL onehot select multiplexer FPV monitor
//
// Testplan:
//
// Design specification:
// - br_mux_onehot is a combinational N-to-1 multiplexer.
// - NumSymbolsIn must be at least 1.
// - SymbolWidth must be at least 1.
// - select is expected to be onehot0 when EnableAssertSelectOnehot is set.
// - When select has exactly one asserted bit, out should equal the selected
//   input symbol.
// - When select is all zero, out should be zero for NumSymbolsIn > 1.
// - When NumSymbolsIn is 1, out should equal the single input regardless of
//   select in synthesis semantics.
// - When EnableAssertSelectOnehot is 0 and select is multihot, output behavior
//   is intentionally undefined. Under SIMULATION, the DUT drives X for that
//   case; formal proof should avoid constraining or asserting a concrete value.
//
// Input assumptions:
// - Parameter legality follows the DUT static assertions.
// - The initial proof milestone should constrain select to onehot0 only for
//   properties that describe defined mux behavior.
//
// Planned summary checks:
// - Defined select values produce the selected input data.
// - Onehot select values produce exactly the selected input symbol.
// - Zero select produces a zero output for multi-input muxes.
// - Parameter sweeps cover single-input, multi-input, narrow, and wider data
//   paths, with EnableAssertSelectOnehot both enabled and disabled.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_mux_onehot_fpv_monitor #(
    parameter int NumSymbolsIn = 1,
    parameter int SymbolWidth = 1,
    parameter bit EnableAssertSelectOnehot = 1
) (
    input logic [NumSymbolsIn-1:0]                  select,
    input logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    input logic [ SymbolWidth-1:0]                  out
);

  if (EnableAssertSelectOnehot) begin : gen_select_onehot0_assume
    // Constrain the primary input to the DUT's defined integration contract.
    `BR_ASSUME_COMB(select_onehot0_a, $onehot0(select))
  end

  if (NumSymbolsIn == 1) begin : gen_single_input_checks
    // A single-input mux must forward its only input under synthesis
    // semantics, regardless of the value of select.
    `BR_ASSERT_COMB(single_input_out_a, out == in[0])

    // Cover the case where the single input is selected.
    `BR_COVER_COMB(single_input_selected_c, select[0])

    // Cover the case where the single input is not selected.
    `BR_COVER_COMB(single_input_unselected_c, !select[0])
  end else begin : gen_multi_input_checks
    // When no input is selected, the OR-reduction should drive zero.
    `BR_ASSERT_COMB(zero_select_out_a, select != '0 || out == '0)

    // Cover the all-zero select case.
    `BR_COVER_COMB(zero_select_c, select == '0)

    if (!EnableAssertSelectOnehot) begin : gen_multihot_allowed_cover
      // Cover the undefined multihot space when the DUT is configured to allow
      // it, without constraining the output value.
      `BR_COVER_COMB(multihot_select_allowed_c, !$onehot0(select))
    end

    for (genvar i = 0; i < NumSymbolsIn; i++) begin : gen_selected_input_checks
      if (EnableAssertSelectOnehot) begin : gen_selected_input_assert
        // Onehot selection of this lane must forward exactly this input symbol.
        `BR_ASSERT_COMB(selected_input_out_a, !select[i] || out == in[i])
      end

      // Cover each input lane being selected.
      `BR_COVER_COMB(selected_input_c, $onehot(select) && select[i])
    end
  end

endmodule : br_mux_onehot_fpv_monitor

bind br_mux_onehot br_mux_onehot_fpv_monitor #(
    .NumSymbolsIn(NumSymbolsIn),
    .SymbolWidth(SymbolWidth),
    .EnableAssertSelectOnehot(EnableAssertSelectOnehot)
) monitor (.*);
