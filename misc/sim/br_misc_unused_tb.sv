// SPDX-License-Identifier: Apache-2.0

/*
 * Testbench for br_misc_unused.
 *
 * Scenarios:
 * - Reset the no-state DUT through br_test_driver.
 * - Drive all-zero and all-one inputs.
 * - Walk a single set bit across every input bit.
 * - Drive NumRandomIterations pseudo-random input values.
 * - Check that the internal reduction sink tracks the OR reduction of in.
 */
module br_misc_unused_tb;

  parameter int Width = 1;
  parameter int NumRandomIterations = 8;

  logic clk;
  logic rst;
  logic [Width-1:0] in;

  br_misc_unused #(.Width(Width)) dut (.in);

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_sink(input string message);
    td.wait_cycles(1);
    td.check(dut.unused === (|in), message);
  endtask

  initial begin
    in = '0;

    td.reset_dut();

    check_sink("sink observes all-zero input");

    in = '1;
    check_sink("sink observes all-one input");

    for (int i = 0; i < Width; i++) begin
      in = '0;
      in[i] = 1'b1;
      check_sink($sformatf("sink observes bit %0d", i));
    end

    for (int i = 0; i < NumRandomIterations; i++) begin
      in = $urandom();
      check_sink($sformatf("sink observes random input %0d", i));
    end

    td.finish();
  end

endmodule : br_misc_unused_tb
