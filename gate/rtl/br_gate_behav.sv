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

// Bedrock-RTL Gate Library Behavioral Models
//
// This file contains behavioral models for the Bedrock-RTL gate library. This
// file is expected to be branched for each vendor technology and behavioral
// models should be replaced with vendor-specific standard cells. Only one
// version of the gatelib should be included in the design filelist.

// TODO: add a mechanism to make sure these modules are never synthesized

// verilog_lint: waive-start module-filename
// ri lint_check_off ONE_PER_FILE FILE_NAME

`include "br_registers.svh"

// Buffer
module br_gate_buf (
    input  logic in,
    output logic out
);

  assign out = in;

endmodule : br_gate_buf

// Clock Buffer
module br_gate_clk_buf (
    input  logic in,
    output logic out
);

  assign out = in;

endmodule : br_gate_clk_buf

// Inverter
module br_gate_inv (
    input  logic in,
    output logic out
);

  assign out = ~in;

endmodule : br_gate_inv

// 2-input AND gate
module br_gate_and2 (
    input  logic in0,
    input  logic in1,
    output logic out
);

  assign out = in0 && in1;

endmodule : br_gate_and2

// 2-input OR gate
module br_gate_or2 (
    input  logic in0,
    input  logic in1,
    output logic out
);

  assign out = in0 || in1;

endmodule : br_gate_or2

// 2-input XOR gate
module br_gate_xor2 (
    input  logic in0,
    input  logic in1,
    output logic out
);

  assign out = in0 ^ in1;

endmodule : br_gate_xor2

// 2-input MUX gate
module br_gate_mux2 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

  assign out = sel ? in1 : in0;

endmodule : br_gate_mux2

// 2-input Clock MUX gate
// This is *not* meant to be a glitchless clock mux. This is simply a stdcell
// mux that can be used to select between two clock sources. Some vendors may
// include a balanced clock tree mux in their standard cell library.
module br_gate_clk_mux2 (
    input  logic in0,
    input  logic in1,
    input  logic sel,
    output logic out
);

  assign out = sel ? in1 : in0;

endmodule : br_gate_clk_mux2

// Integrated Clock Gate with Test Override
module br_gate_icg (
    input  logic clk_in,
    input  logic en,
    output logic clk_out
);

  logic latch_en;

  always_latch begin
    if (!clk_in) begin
      latch_en = en;
    end
  end

  assign clk_out = clk_in & latch_en;

endmodule : br_gate_icg

// Integrated Clock Gate with Test Override and Synchronous Reset
module br_gate_icg_rst (
    input logic clk_in,
    input logic en,
    input logic rst,  // sync reset
    output logic clk_out
);

  logic latch_en;

  always_latch begin
    if (!clk_in) begin
      latch_en = rst | en;
    end
  end

  assign clk_out = clk_in & latch_en;

endmodule : br_gate_icg_rst

// Clock Domain Crossing Synchronizer
module br_gate_cdc_sync #(
    parameter int NumStages = 3
) (
    input  logic clk,
    input  logic in,
    output logic out
);

  logic [NumStages-1:0] in_d;

  `BR_REGN(in_d, {in_d[NumStages-2:0], in})

  assign out = in_d[NumStages-1];
endmodule : br_gate_cdc_sync
// verilog_lint: waive-stop module-filename
// ri lint_check_on ONE_PER_FILE FILE_NAME
