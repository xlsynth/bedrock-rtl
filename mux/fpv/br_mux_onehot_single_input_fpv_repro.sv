// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for the single-input one-hot mux select behavior.

`include "br_asserts.svh"

module br_mux_onehot_single_input_fpv_repro (
    input logic clk,
    input logic rst
);
  logic select;
  logic [0:0][0:0] in;
  logic out;

  br_mux_onehot #(
      .NumSymbolsIn(1),
      .SymbolWidth(1),
      .EnableAssertSelectOnehot(1)
  ) dut (
      .select,
      .in,
      .out
  );

  assign select = 1'b0;
  assign in[0] = 1'b1;

  `BR_ASSERT(no_select_drives_zero_a, !rst |-> out == 1'b0)

endmodule : br_mux_onehot_single_input_fpv_repro
