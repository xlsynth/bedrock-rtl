// SPDX-License-Identifier: Apache-2.0

/*
 * Testbench for br_misc_tieoff_zero.
 *
 * Scenarios:
 * - Reset the no-state DUT through br_test_driver.
 * - Check that the output port width matches the Width parameter.
 * - Check that the output is all zeros after reset and remains stable.
 */
module br_misc_tieoff_zero_tb;

  parameter int Width = 1;

  logic clk;
  logic rst;
  logic [Width-1:0] out;

  br_misc_tieoff_zero #(.Width(Width)) dut (.out);

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    td.reset_dut();
    td.wait_cycles(1);

    td.check($bits(out) == Width, $sformatf("expected output width %0d", Width));
    td.check(out === '0, "out is tied low after reset");

    td.wait_cycles(1);
    td.check(out === '0, "out remains tied low");

    td.finish();
  end

endmodule : br_misc_tieoff_zero_tb
