// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_mux_onehot #(
    // Number of inputs to select among. Must be >= 2.
    parameter int NumSymbolsIn = 2,
    // The width of each symbol in bits. Must be >= 1.
    parameter int SymbolWidth = 1,
    // If 1, assert that the select is, in fact, onehot.
    // If 0, the select can be multi-hot, but in this case,
    // the output will be undefined and driven to X in simulation.
    parameter bit EnableAssertSelectOnehot = 1
) (
    input  logic [NumSymbolsIn-1:0]                  select,
    input  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in,
    output logic [ SymbolWidth-1:0]                  out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_symbols_in_a, NumSymbolsIn >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  if (EnableAssertSelectOnehot) begin : gen_assert_select_onehot
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_INTG(select_onehot0_a, $onehot0(select))
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [SymbolWidth-1:0] out_internal;

  always_comb begin
    out_internal = '0;

    for (int i = 0; i < NumSymbolsIn; i++) begin
      out_internal |= ({SymbolWidth{select[i]}} & in[i]);
    end
  end

`ifdef SIMULATION
  if (EnableAssertSelectOnehot) begin : gen_onehot_out
    assign out = out_internal;
  end else begin : gen_multihot_out
    always_comb begin
      if ($onehot0(select)) begin
        out = out_internal;
      end else begin
        out = 'X;
      end
    end
  end
`else
  assign out = out_internal;
`endif

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

endmodule : br_mux_onehot
