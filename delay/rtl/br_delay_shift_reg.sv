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

// Bedrock-RTL Delay Shift Register
//
// Implements a configurable depth shift register with an enable input.
// The contents of the shift register are initialized to the 'initial_value'
// at reset or upon assertion of the 'reinit' input.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_shift_reg #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 1  // Must be at least 1
) (
    input  logic                            clk,
    input  logic                            rst,
    // value gets set to initial_value on reset or when reinit is asserted
    input  logic                            reinit,
    input  logic [NumStages-1:0][Width-1:0] initial_value,
    output logic [NumStages-1:0][Width-1:0] value,
    // when shift_en is 1, value becomes {value[NumStages-2:0], shift_in}
    input  logic                            shift_en,
    input  logic [    Width-1:0]            shift_in,
    // shift_out is the same as value[NumStages-1]
    output logic [    Width-1:0]            shift_out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_one_a, NumStages >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumStages-1:0][Width-1:0] stages, stages_next;

  if (NumStages == 1) begin : gen_one_stage
    assign stages_next = (reinit) ? initial_value : shift_in;
  end else begin : gen_multi_stage
    assign stages_next = (reinit) ? initial_value : {stages[NumStages-2:0], shift_in};
  end

  `BR_REGIL(stages, stages_next, shift_en | reinit, initial_value)

  assign shift_out = stages[NumStages-1];
  assign value = stages;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(value_shifted_a,
                  (shift_en && !reinit) |-> value == {stages, shift_in})  // relies on truncation
  `BR_ASSERT_IMPL(value_initialized_a, reinit |-> value == initial_value)
  `BR_ASSERT_IMPL(value_stable_a, !shift_en && !reinit |-> $stable(value))

endmodule : br_delay_shift_reg
