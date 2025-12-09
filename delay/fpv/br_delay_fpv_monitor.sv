// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Line

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_delay_fpv_monitor #(
    parameter int Width = 1,
    parameter int NumStages = 0
) (
    input logic                          clk,
    input logic                          rst,
    input logic [  Width-1:0]            in,
    input logic [  Width-1:0]            out,
    input logic [NumStages:0][Width-1:0] out_stages
);

  if (NumStages == 0) begin : gen_zero_delay
    `BR_ASSERT(out_check_a, out == in)
    `BR_ASSERT(out_stages_check_a, out_stages == in)
  end else begin : gen_pos_delay
    `BR_ASSERT(out_check_a, ##NumStages out == $past(in, NumStages))
    `BR_ASSERT(out_stages_check0_a, out_stages[0] == in)
    `BR_ASSERT(out_stages_check1_a, out_stages[NumStages] == out)
  end

endmodule : br_delay_fpv_monitor

bind br_delay br_delay_fpv_monitor #(
    .Width(Width),
    .NumStages(NumStages)
) monitor (.*);
