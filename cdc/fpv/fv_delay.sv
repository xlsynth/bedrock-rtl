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

`include "br_registers.svh"

module fv_delay #(
    parameter int Width = 1,
    parameter int NumStages = 0
) (
    input  logic             clk,
    input  logic             rst,
    input  logic [Width-1:0] in,
    output logic [Width-1:0] out
);

  logic [NumStages:0][Width-1:0] stages;

  assign stages[0] = in;

  for (genvar i = 1; i <= NumStages; i++) begin : gen_stages
    `BR_REG(stages[i], stages[i-1])
  end

  assign out = stages[NumStages];

endmodule : fv_delay
