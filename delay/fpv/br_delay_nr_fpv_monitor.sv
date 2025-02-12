// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL Delay Line (No Reset)

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
