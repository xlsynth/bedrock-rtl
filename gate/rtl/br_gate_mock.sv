// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Gate Library Mock Behavioral Models
//
// This file contains mock behavioral models for the Bedrock-RTL gate library. This
// file is expected to be branched for each vendor technology and behavioral
// models should be replaced with vendor-specific standard cells. Only one
// version of the gatelib should be included in the design filelist.

`ifdef SYNTHESIS
`ifndef BR_PPA_SYNTHESIS
`BR_ASSERT_STATIC(do_not_synthesize_br_gate_mock_modules_a, 0)
`endif
`endif

// verilog_lint: waive-start module-filename
// ri lint_check_off ONE_PER_FILE FILE_NAME RESET_NAME RESET_DRIVER

`include "br_asserts.svh"
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

// Clock Inverter
module br_gate_clk_inv (
    input  logic in,
    output logic out
);

  assign out = ~in;

endmodule : br_gate_clk_inv

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

// 4-input MUX gate
module br_gate_mux4 (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    output logic out
);
  always_comb begin
    unique case (sel)
      2'b00:   out = in0;
      2'b01:   out = in1;
      2'b10:   out = in2;
      2'b11:   out = in3;
      default: out = 'x;
    endcase
  end
endmodule : br_gate_mux4

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

// Integrated Clock Gate
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

// Integrated Clock Gate with Synchronous Reset
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

// Non-scan D flip-flop without reset.
// The state name must retain the _NOSCAN suffix for scan exclusion.
module br_gate_dff_noscan (
    input  logic clk,
    input  logic in,
    output logic out
);

  // The scan-exclusion contract requires the exact uppercase _NOSCAN suffix.
  // ri lint_check_waive VAR_NAME
  logic out_reg_NOSCAN;

  always_ff @(posedge clk) begin
    out_reg_NOSCAN <= in;
  end

  assign out = out_reg_NOSCAN;

endmodule : br_gate_dff_noscan

// Non-scan D flip-flop with active-low asynchronous reset to zero.
// The state name must retain the _NOSCAN suffix for scan exclusion.
module br_gate_dff_arst_noscan (
    input  logic clk,
    input  logic arst_n,
    input  logic in,
    output logic out
);

  // The scan-exclusion contract requires the exact uppercase _NOSCAN suffix.
  // ri lint_check_waive VAR_NAME
  logic out_reg_NOSCAN;

  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      out_reg_NOSCAN <= 1'b0;
    end else begin
      out_reg_NOSCAN <= in;
    end
  end

  assign out = out_reg_NOSCAN;

endmodule : br_gate_dff_arst_noscan

// Clock Domain Crossing Synchronizer
module br_gate_cdc_sync #(
    parameter int NumStages = 3
) (
    input  logic clk,
    input  logic in,
    output logic out
);

  `BR_ASSERT_STATIC(num_stages_must_be_at_least_1_a, NumStages >= 1)

  logic [NumStages-1:0] in_d;

  `BR_REGN(in_d, {in_d[NumStages-2:0], in})

  assign out = in_d[NumStages-1];

endmodule : br_gate_cdc_sync

// Clock Domain Crossing Synchronizer with Asynchronous Reset
module br_gate_cdc_sync_arst #(
    parameter int NumStages = 3  // must be at least 1
) (
    input  logic clk,
    input  logic arst,  // active-high async reset
    input  logic in,
    output logic out
);

  `BR_ASSERT_STATIC(num_stages_must_be_at_least_1_a, NumStages >= 1)

  logic [NumStages-1:0] in_d;

  // ri lint_check_waive RESET_LEVEL CONST_FF
  `BR_REGA(in_d, {in_d[NumStages-2:0], in})

  assign out = in_d[NumStages-1];

endmodule : br_gate_cdc_sync_arst

// Three-stage non-scan clock domain crossing synchronizer without reset.
// All three stages must retain the _NOSCAN suffix for scan exclusion.
module br_gate_cdc_sync_noscan (
    input  logic clk,
    input  logic in,
    output logic out
);

  // The scan-exclusion contract requires the exact uppercase _NOSCAN suffix.
  // ri lint_check_waive VAR_NAME
  logic [2:0] in_d_reg_NOSCAN;

  always_ff @(posedge clk) begin
    in_d_reg_NOSCAN <= {in_d_reg_NOSCAN[1:0], in};
  end

  assign out = in_d_reg_NOSCAN[2];

endmodule : br_gate_cdc_sync_noscan

// Three-stage non-scan synchronizer with active-low asynchronous reset to zero.
// All three stages must retain the _NOSCAN suffix for scan exclusion.
module br_gate_cdc_sync_arstn_noscan (
    input  logic clk,
    input  logic arst_n,
    input  logic in,
    output logic out
);

  // The scan-exclusion contract requires the exact uppercase _NOSCAN suffix.
  // ri lint_check_waive VAR_NAME
  logic [2:0] in_d_reg_NOSCAN;

  // ri lint_check_waive CONST_FF
  always_ff @(posedge clk or negedge arst_n) begin
    if (!arst_n) begin
      in_d_reg_NOSCAN <= '0;
    end else begin
      in_d_reg_NOSCAN <= {in_d_reg_NOSCAN[1:0], in};
    end
  end

  assign out = in_d_reg_NOSCAN[2];

endmodule : br_gate_cdc_sync_arstn_noscan

// Buffer used at CDC crossings but when the signal is considered pseudo-static. In other words,
// this signal will be stable before the destination domain is out of reset and the clock is
// running.
module br_gate_cdc_pseudostatic (
    input  logic in,
    output logic out
);

  br_gate_buf br_gate_buf_dont_touch_cdc_pseudostatic (
      .in (in),
      .out(out)
  );

endmodule : br_gate_cdc_pseudostatic

// Buffer used at CDC crossings that indicate that this crossing would need to be checked for
// max delay (skew checks).
module br_gate_cdc_maxdel (
    input  logic in,
    output logic out
);

  br_gate_buf br_gate_buf_dont_touch_cdc_maxdel (
      .in (in),
      .out(out)
  );

endmodule : br_gate_cdc_maxdel

// verilog_lint: waive-stop module-filename
// ri lint_check_on ONE_PER_FILE FILE_NAME RESET_NAME RESET_DRIVER
