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
`include "br_asserts.svh"

module br_delay #(
    parameter int BitWidth  = 1,  // Must be at least 1
    parameter int NumStages = 0   // Must be at least 0
) (
    input logic clk,
    input logic rst,
    input logic [BitWidth-1:0] in,
    output logic [BitWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(BitWidthMustBeAtLeastOne_A, BitWidth >= 1)
  `BR_ASSERT_STATIC(NumStagesMustBeAtLeastZero_A, NumStages >= 0)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages:0][BitWidth-1:0] stages;

  assign stages[0] = in;

  for (genvar i = 1; i <= NumStages; i++) begin : gen_stages
    `BR_REG(stages[i], stages[i-1])
  end

  assign out = stages[NumStages];

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(delay_A, ##NumStages out == $past(in, NumStages))

endmodule : br_delay
