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
    parameter int BitWidth  = 1,  // Must be at least 1
    parameter int NumStages = 0   // Must be at least 0
) (
    input  logic                clk,
    input  logic                rst,
    input  logic                in_valid_next,
    input  logic [BitWidth-1:0] in,
    output logic                out_valid_next,
    output logic [BitWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(BitWidthMustBeAtLeastOne_A, BitWidth >= 1)
  `BR_ASSERT_STATIC(NumStagesMustBeAtLeastZero_A, NumStages >= 0)

  `BR_COVER_INTG(in_valid_next_C, in_valid_next)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages:0][BitWidth-1:0] stage_valid_next;
  logic [NumStages:0][BitWidth-1:0] stage;

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

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (NumStages == 0) begin : gen_zero_delay
    `BR_ASSERT_IMPL(passthru_A, out_valid_next == in_valid_next && out == in)
  end else begin : gen_pos_delay
    `BR_ASSERT_IMPL(valid_next_delay_A,
                    ##NumStages out_valid_next == $past(in_valid_next, NumStages))
    `BR_ASSERT_IMPL(data_delay_A,
                    in_valid_next |-> ##NumStages out_valid_next ##1 out == $past(in, NumStages))
  end

endmodule : br_delay_valid_next
