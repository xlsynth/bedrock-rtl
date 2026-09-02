// SPDX-License-Identifier: Apache-2.0

// Check positive-edge capture and stability between edges in the no-reset mock.
module br_gate_dff_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  localparam logic [15:0] Pattern = 16'h735a;

  logic clk;
  logic in;
  logic out;
  logic expected;

  br_gate_dff_noscan dut (
      .clk,
      .in,
      .out
  );

  br_test_driver td (
      .clk,
      .rst()
  );

  initial begin
    in = 1'b0;
    td.reset_dut();
    expected = 1'b0;
    td.check(out === expected, "Initial zero input is captured");

    for (int i = 0; i < $bits(Pattern); i++) begin
      in = Pattern[i];
      #1;
      td.check(out === expected, "Input changes do not pass through between edges");
      td.wait_cycles();
      expected = Pattern[i];
      td.check(out === expected, "Output captures input on the rising edge");
      td.check(dut.out_reg_NOSCAN === expected, "The state retains its NOSCAN name");
    end

    td.finish(1);
  end

endmodule : br_gate_dff_noscan_tb
