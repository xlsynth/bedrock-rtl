// SPDX-License-Identifier: Apache-2.0

// Check three-stage latency and asynchronous clearing of every pipeline stage.
module br_gate_cdc_sync_arstn_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  logic clk;
  logic arst_n;
  logic in;
  logic out;

  br_gate_cdc_sync_arstn_noscan dut (
      .clk,
      .arst_n,
      .in,
      .out
  );

  br_test_driver td (
      .clk,
      .rst()
  );

  task automatic check_cycle(input logic next_in, input logic expected);
    in = next_in;
    td.wait_cycles();
    td.check(out === expected, "Output has exactly three stages of sampled latency");
  endtask

  initial begin
    arst_n = 1'b0;
    in = 1'b1;
    td.reset_dut();
    td.check(out === 1'b0, "Reset holds zero despite a high input");

    #1;
    arst_n = 1'b1;
    #1;
    td.check(out === 1'b0, "Reset release does not change the output between edges");
    check_cycle(1'b1, 1'b0);
    check_cycle(1'b1, 1'b0);
    check_cycle(1'b1, 1'b1);
    td.check(dut.in_d_reg_NOSCAN === 3'b111, "All three NOSCAN stages contain ones");

    #1;
    arst_n = 1'b0;
    #1;
    td.check(out === 1'b0, "Asserting active-low reset clears output between edges");
    td.check(dut.in_d_reg_NOSCAN === 3'b000, "Reset clears every NOSCAN stage asynchronously");
    td.wait_cycles(2);
    td.check(out === 1'b0, "Reset overrides input across clock edges");

    arst_n = 1'b1;
    // Stale contents of either earlier stage would make the pulse arrive early.
    check_cycle(1'b1, 1'b0);
    check_cycle(1'b0, 1'b0);
    check_cycle(1'b0, 1'b1);
    check_cycle(1'b0, 1'b0);

    td.finish(1);
  end

endmodule : br_gate_cdc_sync_arstn_noscan_tb
