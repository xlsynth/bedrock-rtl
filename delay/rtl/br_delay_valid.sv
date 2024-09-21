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

// Bedrock-RTL Delay Line (With Valid)
//
// Delays a valid input signal by a fixed number of clock cycles.
// There are NumStages pipeline registers. If NumStages is 0,
// then the output is the input. The valid registers are reset to 0
// but the datapath registers are not. Each datapath register is clock
// gated using the valid signal.

`include "br_registers.svh"
`include "br_asserts.svh"

module br_delay #(
    parameter int BitWidth = 1,  // Must be at least 1
    parameter int NumStages = 0  // Must be at least 0
) (
    input  logic clk,
    input  logic rst,
    input  logic                in_valid,
    input  logic [BitWidth-1:0] in,
    output logic                out_valid,
    output logic [BitWidth-1:0] out
);

    //------------------------------------------
    // Integration checks
    //------------------------------------------
    `BR_ASSERT_STATIC(BitWidthMustBeAtLeastOne_A, BitWidth >= 1)
    `BR_ASSERT_STATIC(NumStagesMustBeAtLeastZero_A, NumStages >= 0)

    `BR_COVER_INTG(in_valid_C, in_valid)

    //------------------------------------------
    // Implementation
    //------------------------------------------
    logic [NumStages:0][BitWidth-1:0] stage_valid;
    logic [NumStages:0][BitWidth-1:0] stage;

    assign stage_valid[0] = in_valid;
    assign stage[0] = in;

    for (int i = 1; i <= NumStages; i++) begin : gen_stages
        `BR_REGN(stage_valid[i], stage_valid[i-1])
        `BR_REGL(stage[i], stage[i-1], stage_valid[i-1])
    end

    assign out_valid = stage_valid[NumStages];
    assign out = stage[NumStages];

    //------------------------------------------
    // Implementation checks
    //------------------------------------------
    `BR_ASSERT_IMPL(valid_delay_A, ##NumStages out_valid == $past(in_valid, NumStages))
    `BR_ASSERT_IMPL(data_delay_A, in_valid |-> ##NumStages out_valid && out == $past(in, NumStages))

endmodule : br_delay
