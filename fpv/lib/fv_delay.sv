// SPDX-License-Identifier: Apache-2.0

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
