// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

`include "br_asserts.svh"
`include "br_gates.svh"

module br_gates_test;

  logic in0;
  logic in1;
  logic mux_sel;
  logic out_buf;
  logic out_clk_buf;
  logic out_clk_inv;
  logic out_inv;
  logic out_and2;
  logic out_or2;
  logic out_xor2;
  logic out_mux;
  logic out_clk_mux;

  `BR_GATE_BUF(out_buf, in0)
  `BR_GATE_CLK_BUF(out_clk_buf, in0)
  `BR_GATE_INV(out_inv, in0)
  `BR_GATE_CLK_INV(out_clk_inv, in0)
  `BR_GATE_AND2(out_and2, in0, in1)
  `BR_GATE_OR2(out_or2, in0, in1)
  `BR_GATE_XOR2(out_xor2, in0, in1)
  `BR_GATE_MUX2(out_mux, in0, in1, mux_sel)
  `BR_GATE_CLK_MUX2(out_clk_mux, in0, in1, mux_sel)


  `BR_ASSERT_COMB(out_buf_check, out_buf == in0)
  `BR_ASSERT_COMB(out_clk_buf_check, out_clk_buf == in0)
  `BR_ASSERT_COMB(out_inv_check, out_inv == ~in0)
  `BR_ASSERT_COMB(out_clk_inv_check, out_clk_inv == ~in0)
  `BR_ASSERT_COMB(out_and2_check, out_and2 == (in0 & in1))
  `BR_ASSERT_COMB(out_or2_check, out_or2 == (in0 | in1))
  `BR_ASSERT_COMB(out_xor2_check, out_xor2 == (in0 ^ in1))
  `BR_ASSERT_COMB(out_mux_check, out_mux == (mux_sel ? in1 : in0))
  `BR_ASSERT_COMB(out_clk_mux_check, out_clk_mux == (mux_sel ? in1 : in0))


  initial begin
    in0 = 1'b0;
    in1 = 1'b0;
    mux_sel = 1'b0;

    #5 in0 = 1'b1;
    #5 mux_sel = 1'b1;
    #5 in1 = 1'b1;
    #5 in0 = 1'b0;
    #5 mux_sel = 1'b0;

    $finish;
  end

endmodule : br_gates_test
