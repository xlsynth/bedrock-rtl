// Copyright 2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// verilog_lint: waive-start line-length

module br_ram_initializer_gen_unittest;
  timeunit 1ns; timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  parameter int CLOCK_FREQ = 100;  // Clock frequency in MHz
  parameter int RESET_DURATION = 100;  // Reset duration in ns
  parameter int TIMEOUT = 10000000;  // Timeout value in ns
  parameter int PER_TASK_TIMEOUT = 1000000;  // Timeout value for each task in ns
  parameter int DRAIN_TIME = 10000;  // Time to observe all results in ns
  parameter int CLOCK_FREQ_NS_CONVERSION_FACTOR = 1000;  // Conversion factor to nanoseconds
  parameter bit NO_ASSERTS_ON_RESET = 0;  // Disable assertions during reset
  // verilog_lint: waive positive-meaning-parameter-name
  parameter bit DISABLE_CHECKS = 0;  // Disable checks

  //===========================================================
  // DUT Imports and Includes
  //===========================================================

  `include "br_registers.svh"
  `include "br_asserts_internal.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int Depth = 2;
  parameter int Width = 1;
  localparam int AddressWidth = $clog2(Depth);

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [Width-1:0] initial_value;
  logic start;
  logic busy;
  logic wr_valid;
  logic [AddressWidth-1:0] wr_addr;
  logic [Width-1:0] wr_data;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_ram_initializer #(
      .Depth(Depth),
      .Width(Width)
  ) dut (
      .clk(clk),
      .rst(rst),
      .initial_value(initial_value),
      .start(start),
      .busy(busy),
      .wr_valid(wr_valid),
      .wr_addr(wr_addr),
      .wr_data(wr_data)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  int test_failed = -1;

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, initial_value, start;
    input busy, wr_valid, wr_addr, wr_data;
  endclocking


  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    if (NO_ASSERTS_ON_RESET) $assertoff;
    #(TIMEOUT);
    $display("Error: Testbench timeout!");
    $finish;
  end

  //===========================================================
  // Reset Generation
  //===========================================================
  task automatic reset_dut;
    if (NO_ASSERTS_ON_RESET) $assertoff;
    // Set all the DUT inputs to zero, making sure there are no X/Z at the inputs.
    cb_clk.initial_value <= 'h0;
    cb_clk.start <= 'h0;

    // Wiggling the reset signal.
    rst = 1'b0;
    #RESET_DURATION;
    rst = 1'b1;
    #RESET_DURATION;
    rst = 1'b0;
    #RESET_DURATION;
    if (NO_ASSERTS_ON_RESET) $asserton;
  endtask

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
    reset_dut();
    test_InitializeRamWithInitialValue();

    $finish;
  end

  task automatic test_InitializeRamWithInitialValue;
    // Purpose: Test the RAM initialization process by writing a specified initial value to each entry from address 0 to Depth-1.

    // Local variables declaration
    int test_failed = -1;
    logic [AddressWidth-1:0] expected_wr_addr;
    logic [Width-1:0] expected_wr_data;
    int i;

    // Set initial conditions
    cb_clk.initial_value <= $urandom();
    expected_wr_addr = 0;
    expected_wr_data = cb_clk.initial_value;

    // Wait for a clock cycle to ensure proper stimulus propagation
    @(cb_clk);

    // Apply initial value and start the initialization process
    cb_clk.initial_value <= initial_value;
    cb_clk.start <= 1;
    $display(
        "Time: %0t, INFO: test_InitializeRamWithInitialValue - Driving initial_value=0x%h, start=1",
        $time, initial_value);

    // Wait for a clock cycle to capture the start of initialization
    @(cb_clk);
    cb_clk.start <= 0;

    // Check if busy is asserted
    if (cb_clk.busy !== 1) begin
      $display(
          "Time: %0t, ERROR: test_InitializeRamWithInitialValue - Check failed. Expected busy=1, got busy=%b",
          $time, busy);
      test_failed = 1;
    end else begin
      $display(
          "Time: %0t, INFO: test_InitializeRamWithInitialValue - Check passed. Expected busy=1 is the same as the observed value (both are 1).",
          $time);
      if (test_failed != 1) test_failed = 0;
    end

    // Loop through each address and verify initialization
    for (i = 0; i < Depth; i++) begin
      @(cb_clk);

      // Check wr_valid, wr_addr, and wr_data
      if (cb_clk.wr_valid !== 1 || cb_clk.wr_addr !== expected_wr_addr || cb_clk.wr_data !== expected_wr_data) begin
        $display(
            "Time: %0t, ERROR: test_InitializeRamWithInitialValue - Check failed. Expected wr_valid=1, wr_addr=0x%h, wr_data=0x%h, got wr_valid=%b, wr_addr=0x%h, wr_data=0x%h",
            $time, expected_wr_addr, expected_wr_data, cb_clk.wr_valid, cb_clk.wr_addr,
            cb_clk.wr_data);
        test_failed = 1;
      end else begin
        $display(
            "Time: %0t, INFO: test_InitializeRamWithInitialValue - Check passed. Expected wr_valid=1, wr_addr=0x%h, wr_data=0x%h is the same as the observed values.",
            $time, expected_wr_addr, expected_wr_data);
        if (test_failed != 1) test_failed = 0;
      end

      // Increment expected address
      expected_wr_addr++;
    end

    // Wait for busy to be deasserted
    @(cb_clk);
    if (cb_clk.busy !== 0) begin
      $display(
          "Time: %0t, ERROR: test_InitializeRamWithInitialValue - Check failed. Expected busy=0, got busy=%b",
          $time, busy);
      test_failed = 1;
    end else begin
      $display(
          "Time: %0t, INFO: test_InitializeRamWithInitialValue - Check passed. Expected busy=0 is the same as the observed value (both are 0).",
          $time);
      if (test_failed != 1) test_failed = 0;
    end

    // Report test status
    if (test_failed == 0) begin
      $display("Time: %0t, PASSED: test_InitializeRamWithInitialValue", $time);
    end else begin
      $display("Time: %0t, FAILED: test_InitializeRamWithInitialValue", $time);
    end
  endtask
endmodule

// verilog_lint: waive-stop line-length
