// SPDX-License-Identifier: Apache-2.0

`include "br_registers.svh"

// Check the explicit-clock macro family with vector, scalar, and packed data.
module br_registers_noscan_tb;
  timeunit 1ns; timeprecision 1ps;

  parameter int Width = 8;

  logic reg_clk;
  logic sync_rst;
  logic async_rst;
  logic en;
  logic [Width-1:0] data;
  logic [Width-1:0] q_no_reset;
  logic [Width-1:0] q_sync;
  logic [Width-1:0] q_sync_en;
  logic [Width-1:0] q_async;
  logic [Width-1:0] q_async_en;
  logic [Width-1:0] q_narrow_no_reset;
  logic [Width-1:0] q_narrow_sync;
  logic [Width-1:0] q_narrow_sync_en;
  logic [Width-1:0] q_narrow_async;
  logic [Width-1:0] q_narrow_async_en;
  logic q_scalar;
  logic [1:0][Width-1:0] q_packed;
  logic [Width-1:0] pattern;

  br_test_driver td (
      .clk(reg_clk),
      .rst()
  );

  `BR_REGNX_NOSCAN(q_no_reset, data, reg_clk)
  `BR_REGX_NOSCAN(q_sync, data, reg_clk, sync_rst)
  `BR_REGLX_NOSCAN(q_sync_en, data, en, reg_clk, sync_rst)
  `BR_REGAX_NOSCAN(q_async, data, reg_clk, async_rst)
  `BR_REGALX_NOSCAN(q_async_en, data, en, reg_clk, async_rst)

  // A one-bit input must be zero-extended, not broadcast to every gate instance.
  `BR_REGNX_NOSCAN(q_narrow_no_reset, data[0], reg_clk)
  `BR_REGX_NOSCAN(q_narrow_sync, data[0], reg_clk, sync_rst)
  `BR_REGLX_NOSCAN(q_narrow_sync_en, data[0], en, reg_clk, sync_rst)
  `BR_REGAX_NOSCAN(q_narrow_async, data[0], reg_clk, async_rst)
  `BR_REGALX_NOSCAN(q_narrow_async_en, data[0], en, reg_clk, async_rst)

  `BR_REGNX_NOSCAN(q_scalar, ~data[0], reg_clk)
  `BR_REGNX_NOSCAN(q_packed, {~data, data}, reg_clk)

  task automatic check_outputs(
      input logic [Width-1:0] expected_no_reset, input logic [Width-1:0] expected_sync,
      input logic [Width-1:0] expected_sync_en, input logic [Width-1:0] expected_async,
      input logic [Width-1:0] expected_async_en);
    td.check(q_no_reset === expected_no_reset, "BR_REGNX_NOSCAN output");
    td.check(q_sync === expected_sync, "BR_REGX_NOSCAN output");
    td.check(q_sync_en === expected_sync_en, "BR_REGLX_NOSCAN output");
    td.check(q_async === expected_async, "BR_REGAX_NOSCAN output");
    td.check(q_async_en === expected_async_en, "BR_REGALX_NOSCAN output");
    td.check(q_narrow_no_reset === Width'(expected_no_reset[0]), "No-reset input extension");
    td.check(q_narrow_sync === Width'(expected_sync[0]), "Synchronous input extension");
    td.check(q_narrow_sync_en === Width'(expected_sync_en[0]),
             "Enabled synchronous input extension");
    td.check(q_narrow_async === Width'(expected_async[0]), "Asynchronous input extension");
    td.check(q_narrow_async_en === Width'(expected_async_en[0]),
             "Enabled asynchronous input extension");
    td.check(q_scalar === ~expected_no_reset[0], "Scalar output and input expression");
    td.check(q_packed === {~expected_no_reset, expected_no_reset},
             "Packed output and concatenation");
    td.check(q_no_reset_reg_NOSCAN[0].out_reg_NOSCAN === expected_no_reset[0],
             "Macro instantiates the named NOSCAN gate state");
  endtask

  initial begin
    data = '0;
    en = 1'b0;
    sync_rst = 1'b1;
    async_rst = 1'b1;
    td.reset_dut();
    check_outputs('0, '0, '0, '0, '0);

    sync_rst = 1'b0;
    async_rst = 1'b0;
    en = 1'b1;
    data = '1;
    td.wait_cycles();
    check_outputs('1, '1, '1, '1, '1);

    en   = 1'b0;
    data = '0;
    #1;
    check_outputs('1, '1, '1, '1, '1);
    td.wait_cycles();
    check_outputs('0, '0, '1, '0, '1);

    en   = 1'b1;
    data = '1;
    td.wait_cycles();
    check_outputs('1, '1, '1, '1, '1);

    // Reset has priority over a disabled load. Only async outputs clear now.
    en = 1'b0;
    sync_rst = 1'b1;
    async_rst = 1'b1;
    #1;
    check_outputs('1, '1, '1, '0, '0);
    data = '0;
    td.wait_cycles();
    check_outputs('0, '0, '0, '0, '0);

    // Reset also overrides enabled loads with nonzero data.
    en   = 1'b1;
    data = '1;
    td.wait_cycles();
    check_outputs('1, '0, '0, '0, '0);

    en = 1'b0;
    sync_rst = 1'b0;
    async_rst = 1'b0;
    #1;
    check_outputs('1, '0, '0, '0, '0);
    td.wait_cycles();
    check_outputs('1, '1, '0, '1, '0);

    // Exercise each bit, including bits above integer width, and disabled holds.
    for (int i = 0; i < Width; i++) begin
      pattern = '0;
      pattern[i] = 1'b1;
      en = 1'b1;
      data = pattern;
      td.wait_cycles();
      check_outputs(pattern, pattern, pattern, pattern, pattern);
      en   = 1'b0;
      data = ~pattern;
      td.wait_cycles();
      check_outputs(~pattern, ~pattern, pattern, ~pattern, pattern);
    end

    td.finish(1);
  end

endmodule : br_registers_noscan_tb
