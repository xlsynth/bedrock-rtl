// SPDX-License-Identifier: Apache-2.0

// Check that the mock delays each sampled input through exactly three flops.
module br_gate_cdc_sync_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  localparam logic [23:0] Pattern = 24'h1d36a1;

  logic clk;
  logic in;
  logic out;

  br_gate_cdc_sync_noscan dut (
      .clk,
      .in,
      .out
  );

  br_test_driver td (
      .clk,
      .rst()
  );

  task automatic check_cycle(input logic next_in, input logic expected);
    logic previous_out;
    previous_out = out;
    in = next_in;
    #1;
    td.check(out === previous_out, "Input changes do not pass through between edges");
    td.wait_cycles();
    td.check(out === expected, "Output has exactly three stages of sampled latency");
  endtask

  initial begin
    in = 1'b0;
    td.reset_dut();
    td.wait_cycles(3);
    td.check(out === 1'b0, "Zero input flushes the no-reset synchronizer");
    td.check(dut.in_d_reg_NOSCAN === 3'b000, "All three state bits retain the NOSCAN name");

    // A one-cycle pulse must appear only at the third sampling edge.
    check_cycle(1'b1, 1'b0);
    check_cycle(1'b0, 1'b0);
    check_cycle(1'b0, 1'b1);
    check_cycle(1'b0, 1'b0);

    for (int i = 0; i < $bits(Pattern) + 2; i++) begin
      check_cycle(i < $bits(Pattern) ? Pattern[i] : 1'b0, i >= 2 ? Pattern[i-2] : 1'b0);
    end

    td.finish(1);
  end

endmodule : br_gate_cdc_sync_noscan_tb
