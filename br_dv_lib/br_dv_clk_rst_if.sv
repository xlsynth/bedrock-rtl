// SPDX-License-Identifier: Apache-2.0

interface br_dv_clk_rst_if #(
    parameter int ClockPeriodNs = 10
);
  logic clk;
  logic rst;

  initial clk = 1'b0;
  always #(ClockPeriodNs / 2) clk = ~clk;

  initial rst = 1'b1;
endinterface
