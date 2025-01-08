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

// Bedrock-RTL Delay Line (With Valid-Next)
//
// Delays a valid input signal by a fixed number of clock cycles.
// There are NumStages pipeline registers. If NumStages is 0,
// then the output is the input. The valid registers are reset
// to 0 but the datapath registers are not reset. Each datapath register is
// clock gated using the valid_next signal.
//
// valid_next runs one cycle ahead of the data, i.e., if valid_next is 1 then
// the data is valid on the following cycle. This can be very useful for closing
// timing on a wide bus that covers a long wire distance. The width-wise fanout
// delay is on a different cycle than the lengthwise wire delay.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_valid_next #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0  // Must be at least 0
) (
    // Positive edge-triggered. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          clk,
    // Synchronous active-high. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          rst,
    input  logic                          in_valid_next,
    input  logic [  Width-1:0]            in,
    output logic                          out_valid_next,
    output logic [  Width-1:0]            out,
    // Indicates the valid_next signal at each stage.
    output logic [NumStages:0]            out_valid_next_stages,
    // Output of each delay stage. Note that out_stages[0] == in, and
    // out_stages[NumStages] == out.
    output logic [NumStages:0][Width-1:0] out_stages
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_zero_a, NumStages >= 0)

  `BR_COVER_INTG(in_valid_next_c, in_valid_next)

  `BR_ASSERT_FINAL(final_not_in_valid_next_a, !in_valid_next)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages:0] stage_valid_next;
  logic [NumStages:0][Width-1:0] stage;

  assign stage_valid_next[0] = in_valid_next;
  assign stage[0] = in;

  for (genvar i = 1; i <= NumStages; i++) begin : gen_stages
    `BR_REG(stage_valid_next[i], stage_valid_next[i-1])
    // stage_valid_next[i] is equivalent to hypothetical stage_valid[i-1],
    // which would be aligned to stage[i-1].
    `BR_REGLN(stage[i], stage[i-1], stage_valid_next[i])
  end

  assign out_valid_next = stage_valid_next[NumStages];
  assign out = stage[NumStages];
  assign out_valid_next_stages = stage_valid_next;
  assign out_stages = stage;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (NumStages == 0) begin : gen_zero_delay
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_IMPL(valid_passthru_a, out_valid_next === in_valid_next)
    // ri lint_check_waive ALWAYS_COMB
    `BR_ASSERT_COMB_IMPL(data_passthru_a, out === in)
  end else begin : gen_pos_delay
    `BR_ASSERT_IMPL(valid_next_delay_a,
                    ##NumStages out_valid_next == $past(in_valid_next, NumStages))
    `BR_ASSERT_IMPL(data_delay_a,
                    in_valid_next |-> ##NumStages out_valid_next ##1 out == $past(in, NumStages))
  end

  `BR_ASSERT_FINAL(final_not_out_valid_next_a, !out_valid_next)

endmodule : br_delay_valid_next
