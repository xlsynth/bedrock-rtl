// SPDX-License-Identifier: Apache-2.0

// Check active-low asynchronous reset independently of clock edges.
module br_gate_dff_arst_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  logic clk;
  logic arst_n;
  logic in;
  logic out;

  br_gate_dff_arst_noscan dut (
      .clk,
      .arst_n,
      .in,
      .out
  );

  br_test_driver td (
      .clk,
      .rst()
  );

  initial begin
    arst_n = 1'b0;
    in = 1'b1;
    td.reset_dut();
    td.check(out === 1'b0, "Reset holds zero despite a high input");

    #1;
    arst_n = 1'b1;
    #1;
    td.check(out === 1'b0, "Releasing reset does not capture input before an edge");
    td.wait_cycles();
    td.check(out === 1'b1, "High input is captured after reset release");

    #1;
    arst_n = 1'b0;
    #1;
    td.check(out === 1'b0, "Asserting active-low reset clears output between edges");
    td.check(dut.out_reg_NOSCAN === 1'b0, "The NOSCAN state clears asynchronously");
    td.wait_cycles(2);
    td.check(out === 1'b0, "Reset overrides high input across clock edges");

    arst_n = 1'b1;
    td.wait_cycles();
    td.check(out === 1'b1, "Capture resumes when reset is released");
    in = 1'b0;
    #1;
    td.check(out === 1'b1, "Input changes do not pass through between edges");
    td.wait_cycles();
    td.check(out === 1'b0, "Low input is captured on the next rising edge");

    td.finish(1);
  end

endmodule : br_gate_dff_arst_noscan_tb
