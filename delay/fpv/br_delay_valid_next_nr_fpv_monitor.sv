// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Line (With Valid-Next, No Reset)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_delay_valid_next_nr_fpv_monitor #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0,  // Must be at least 0
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                          clk,
    input logic                          in_valid_next,
    input logic [  Width-1:0]            in,
    input logic                          out_valid_next,
    input logic [  Width-1:0]            out,
    input logic [NumStages:0]            out_valid_next_stages,
    input logic [NumStages:0][Width-1:0] out_stages
);

  if (NumStages == 0) begin : gen_zero_delay
    // out valid_next/payload checks
    `BR_ASSERT_CR(out_valid_next_check_a, out_valid_next == in_valid_next, clk, 1'b0)
    `BR_ASSERT_CR(out_check_a, out == in, clk, 1'b0)
    // stage valid_next/payload check
    `BR_ASSERT_CR(out_valid_next_stages_check_a, out_valid_next_stages == in_valid_next, clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check_a, out_stages == in, clk, 1'b0)
  end else begin : gen_pos_delay
    // out valid_next/payload check
    // in_valid and out_valid has NumStages of delay
    // in and out has NumStages of delay
    // valid and payload has 1 cycle delay
    `BR_ASSERT_CR(out_valid_next_check_a,
                  ##NumStages out_valid_next == $past(in_valid_next, NumStages), clk, 1'b0)
    `BR_ASSERT_CR(out_check_a, in_valid_next |=> ##NumStages out == $past(in, NumStages), clk, 1'b0)
    // stage valid_next/payload check
    `BR_ASSERT_CR(out_valid_next_stages_check0_a, out_valid_next_stages[0] == in_valid_next, clk,
                  1'b0)
    `BR_ASSERT_CR(out_valid_next_stages_check1_a,
                  out_valid_next_stages[NumStages] == out_valid_next, clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check0_a, out_stages[0] == in, clk, 1'b0)
    `BR_ASSERT_CR(out_stages_check1_a, out_stages[NumStages] == out, clk, 1'b0)
  end

endmodule : br_delay_valid_next_nr_fpv_monitor

bind br_delay_valid_next_nr br_delay_valid_next_nr_fpv_monitor #(
    .Width(Width),
    .NumStages(NumStages),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
