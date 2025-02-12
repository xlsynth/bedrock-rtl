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

// Bedrock-RTL Delay Line (With Valid)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_delay_valid_fpv_monitor #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0,  // Must be at least 0
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                          clk,
    input logic                          rst,
    input logic                          in_valid,
    input logic [  Width-1:0]            in,
    input logic                          out_valid,
    input logic [  Width-1:0]            out,
    input logic [NumStages:0]            out_valid_stages,
    input logic [NumStages:0][Width-1:0] out_stages
);

  if (NumStages == 0) begin : gen_zero_delay
    // out valid/payload check
    `BR_ASSERT(out_valid_check_a, out_valid == in_valid)
    `BR_ASSERT(out_check_a, out == in)
    // stage valid/payload check
    `BR_ASSERT(out_valid_stages_check_a, out_valid_stages == in_valid)
    `BR_ASSERT(out_stages_check_a, out_stages == in)
  end else begin : gen_pos_delay
    // out valid/payload check
    `BR_ASSERT(out_valid_check_a, ##NumStages out_valid == $past(in_valid, NumStages))
    `BR_ASSERT(out_check_a, in_valid |-> ##NumStages out == $past(in, NumStages))
    // stage valid/payload check
    `BR_ASSERT(out_valid_stages_check0_a, out_valid_stages[0] == in_valid)
    `BR_ASSERT(out_valid_stages_check1_a, out_valid_stages[NumStages] == out_valid)
    `BR_ASSERT(out_stages_check0_a, out_stages[0] == in)
    `BR_ASSERT(out_stages_check1_a, out_stages[NumStages] == out)
  end

endmodule : br_delay_valid_fpv_monitor

bind br_delay_valid br_delay_valid_fpv_monitor #(
    .Width(Width),
    .NumStages(NumStages),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
