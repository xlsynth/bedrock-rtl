// SPDX-License-Identifier: Apache-2.0


// Unit test for br_multicycle_path.svh macros

`timescale 1ns / 1ps

`include "br_multicycle_path.svh"

module br_cdc_multicycle_path_tb ();

  localparam int Width = 4;
  localparam int ClkPeriod = 10;
  localparam int ClkHalfPeriod = ClkPeriod / 2;
  localparam int MaxCaptureCycleDelay = 3;
  localparam logic [Width-1:0] StableValue = 4'hc;

  logic clk;
  logic rst;
  logic [Width-1:0] driven_in;
  logic [Width-1:0] out_1_1;
  logic [Width-1:0] out_2_1;
  logic [Width-1:0] out_2_2;
  logic [Width-1:0] out_3_1;
  logic [Width-1:0] out_3_2;
  logic [Width-1:0] out_3_3;
  logic [Width-1:0] reset_only_out;
  logic [Width-1:0] named_reset_only_out;
  logic [Width-1:0] in_history[MaxCaptureCycleDelay];
  int cycle_count;
  int error_count;

  // Macro coverage for the default CaptureCyclesWidth = CaptureCycleDelay.
  `BR_MCP(1, driven_in, out_1_1)
  `BR_MCP_NAMED(shift2_default, 2, driven_in, out_2_2)
  `BR_MCP_NAMED(shift3_default, 3, driven_in, out_3_3)

  // Direct instantiations for non-default CaptureCyclesWidth values.
  br_cdc_multicycle_path #(
      .Width(Width),
      .CaptureCycleDelay(2),
      .CaptureCyclesWidth(1)
  ) br_cdc_multicycle_path_2_1 (
      .clk,
      .rst,
      .in (driven_in),
      .out(out_2_1)
  );

  br_cdc_multicycle_path #(
      .Width(Width),
      .CaptureCycleDelay(3),
      .CaptureCyclesWidth(1)
  ) br_cdc_multicycle_path_3_1 (
      .clk,
      .rst,
      .in (driven_in),
      .out(out_3_1)
  );

  br_cdc_multicycle_path #(
      .Width(Width),
      .CaptureCycleDelay(3),
      .CaptureCyclesWidth(2)
  ) br_cdc_multicycle_path_3_2 (
      .clk,
      .rst,
      .in (driven_in),
      .out(out_3_2)
  );

  // Keep the reset-only macro variants instantiated with a stable source.
  `BR_RESET_ONLY_MCP(2, StableValue, reset_only_out)
  `BR_RESET_ONLY_MCP_NAMED(named_reset_only_path, 3, StableValue, named_reset_only_out)

  always #ClkHalfPeriod clk = ~clk;

  function automatic logic [Width-1:0] get_expected_stage(input int stage_index);
    if (stage_index <= 1) begin
      return in_history[0];
    end

    return in_history[stage_index-1];
  endfunction

  function automatic logic [Width-1:0] get_expected_output(input int capture_cycle_delay,
                                                           input int capture_cycles_width);
    logic [Width-1:0] delayed_value;

    delayed_value = get_expected_stage(capture_cycle_delay - 1);
    for (int i = 0; i < capture_cycles_width; i++) begin
      if (delayed_value != get_expected_stage(capture_cycle_delay - 1 - i)) begin
        return 'x;
      end
    end

    return delayed_value;
  endfunction

  task automatic check_output(input string name, input logic [Width-1:0] actual,
                              input logic [Width-1:0] expected);
    if (actual !== expected) begin
      error_count++;
      $error("Cycle %0d: %0s expected %0h but got %0h", cycle_count, name, expected, actual);
    end
  endtask

  task automatic drive_and_check(input logic [Width-1:0] next_in);
    @(negedge clk);
    driven_in = next_in;

    @(posedge clk);
    cycle_count++;
    for (int i = MaxCaptureCycleDelay - 1; i > 0; i--) begin
      in_history[i] = in_history[i-1];
    end
    in_history[0] = next_in;

    #1;
    check_output("(1,1)", out_1_1, get_expected_output(1, 1));
    check_output("(2,1)", out_2_1, get_expected_output(2, 1));
    check_output("(2,2)", out_2_2, get_expected_output(2, 2));
    check_output("(3,1)", out_3_1, get_expected_output(3, 1));
    check_output("(3,2)", out_3_2, get_expected_output(3, 2));
    check_output("(3,3)", out_3_3, get_expected_output(3, 3));
    check_output("reset_only_(2,2)", reset_only_out, StableValue);
    check_output("reset_only_(3,3)", named_reset_only_out, StableValue);
  endtask

  task automatic prime_duts();
    driven_in = '0;
    for (int i = 0; i < MaxCaptureCycleDelay; i++) begin
      in_history[i] = '0;
    end

    repeat (MaxCaptureCycleDelay + 1) begin
      @(negedge clk);
      driven_in = '0;
      @(posedge clk);
    end
  endtask

  initial begin
    clk = 1'b0;
    rst = 1'b1;
    driven_in = '0;
    cycle_count = 0;
    error_count = 0;

`ifndef SIMULATION
    $fatal(1, "br_cdc_multicycle_path_tb requires SIMULATION to validate delay behavior");
`endif

    prime_duts();
    @(negedge clk);
    rst = 1'b0;

    drive_and_check(4'h1);
    drive_and_check(4'h2);
    drive_and_check(4'h3);
    drive_and_check(4'h4);
    drive_and_check(4'h4);
    drive_and_check(4'h4);

    if (error_count != 0) begin
      $fatal(1, "br_cdc_multicycle_path_tb failed with %0d errors", error_count);
    end

    $display("TEST PASSED");
    $finish;
  end

endmodule : br_cdc_multicycle_path_tb
