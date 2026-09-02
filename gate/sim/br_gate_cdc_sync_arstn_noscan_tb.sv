// SPDX-License-Identifier: Apache-2.0

// Check configured latency and asynchronous clearing of every pipeline stage.
module br_gate_cdc_sync_arstn_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  parameter int NumStages = 3;

  logic clk;
  logic arst_n;
  logic in;
  logic out;

  br_gate_cdc_sync_arstn_noscan #(
      .NumStages(NumStages)
  ) dut (
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
    td.check(out === expected, "Output has the configured number of sampled stages");
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
    for (int i = 0; i < NumStages; i++) begin
      check_cycle(1'b1, i == NumStages - 1);
    end
    td.check(dut.in_d_reg_NOSCAN === '1, "All NOSCAN stages contain ones");

    #1;
    arst_n = 1'b0;
    #1;
    td.check(out === 1'b0, "Asserting active-low reset clears output between edges");
    td.check(dut.in_d_reg_NOSCAN === '0, "Reset clears every NOSCAN stage asynchronously");
    td.wait_cycles(NumStages);
    td.check(out === 1'b0, "Reset overrides input across clock edges");

    arst_n = 1'b1;
    // Stale contents of any earlier stage would make the pulse arrive early.
    for (int i = 0; i <= NumStages; i++) begin
      check_cycle(i == 0, i == NumStages - 1);
    end

    td.finish(1);
  end

endmodule : br_gate_cdc_sync_arstn_noscan_tb
