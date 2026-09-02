// SPDX-License-Identifier: Apache-2.0

// Check that the mock delays each sampled input through the configured flops.
module br_gate_cdc_sync_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  parameter int NumStages = 3;

  localparam logic [23:0] Pattern = 24'h1d36a1;

  logic clk;
  logic in;
  logic out;

  br_gate_cdc_sync_noscan #(
      .NumStages(NumStages)
  ) dut (
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
    td.check(out === expected, "Output has the configured number of sampled stages");
  endtask

  initial begin
    in = 1'b0;
    td.reset_dut();
    td.wait_cycles(NumStages);
    td.check(out === 1'b0, "Zero input flushes the no-reset synchronizer");
    td.check(dut.in_d_reg_NOSCAN === '0, "All state bits retain the NOSCAN name");

    // A one-cycle pulse appears only at the NumStages-th sampling edge.
    for (int i = 0; i <= NumStages; i++) begin
      check_cycle(i == 0, i == NumStages - 1);
    end

    for (int i = 0; i < $bits(Pattern) + NumStages - 1; i++) begin
      check_cycle(i < $bits(Pattern) ? Pattern[i] : 1'b0,
                  i >= NumStages - 1 ? Pattern[i-(NumStages-1)] : 1'b0);
    end

    td.finish(1);
  end

endmodule : br_gate_cdc_sync_noscan_tb
