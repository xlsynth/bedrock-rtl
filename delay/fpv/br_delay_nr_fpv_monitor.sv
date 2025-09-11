// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_delay_nr_fpv_monitor #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0  // Must be at least 0
) (
    input logic                          clk,
    input logic [  Width-1:0]            in,
    input logic [  Width-1:0]            out,
    input logic [NumStages:0][Width-1:0] out_stages
);

  if (NumStages == 0) begin : gen_zero_delay
    `BR_ASSERT_CR(out_check_a, out == in, clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check_a, out_stages == in, clk, 1'b0)
  end else begin : gen_pos_delay
    `BR_ASSERT_CR(out_check_a, ##NumStages out == $past(in, NumStages), clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check0_a, out_stages[0] == in, clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check1_a, out_stages[NumStages] == out, clk, 1'b0)
  end

endmodule : br_delay_nr_fpv_monitor

bind br_delay_nr br_delay_nr_fpv_monitor #(
    .Width(Width),
    .NumStages(NumStages)
) monitor (.*);
