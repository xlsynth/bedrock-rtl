// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Delay Line
//
// Delays an input signal by a fixed number of clock cycles.
// There are NumStages pipeline registers. If NumStages is 0,
// then the output is the input. The pipeline registers are reset
// to 0.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0  // Must be at least 0
) (
    // Positive edge-triggered. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          clk,
    // Synchronous active-high. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          rst,
    input  logic [  Width-1:0]            in,
    // Output of last delay stage (delayed by NumStages cycles).
    output logic [  Width-1:0]            out,
    // Output of each delay stage. Note that out_stages[0] == in, and
    // out_stages[NumStages] == out.
    output logic [NumStages:0][Width-1:0] out_stages
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_zero_a, NumStages >= 0)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages:0][Width-1:0] stages;

  assign stages[0] = in;

  for (genvar i = 1; i <= NumStages; i++) begin : gen_stages
    `BR_REG(stages[i], stages[i-1])
  end

  assign out = stages[NumStages];
  assign out_stages = stages;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (NumStages == 0) begin : gen_zero_delay
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_IMPL(passthru_a, out === in)
  end else begin : gen_pos_delay
    `BR_ASSERT_IMPL(delay_a, ##NumStages out == $past(in, NumStages))
  end


endmodule : br_delay
