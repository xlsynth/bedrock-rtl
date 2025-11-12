// SPDX-License-Identifier: Apache-2.0


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
  parameter int Width = 3;
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
  bit test_failed = 0;

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
    rst = 1'bx;
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

    if (test_failed) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end

  task automatic test_InitializeRamWithInitialValue;
    // Purpose: Test the RAM initialization process by writing a specified initial value to each entry from address 0 to Depth-1.

    // Local variables declaration
    int errors = 0;
    logic [AddressWidth-1:0] expected_wr_addr;
    logic [Width-1:0] tb_initial_value;
    logic [Width-1:0] expected_wr_data;
    int i;

    // Set initial conditions
    tb_initial_value = $urandom();
    expected_wr_addr = 0;
    expected_wr_data = tb_initial_value;

    cb_clk.initial_value <= tb_initial_value;

    // Wait for a clock cycle to ensure proper stimulus propagation
    @(cb_clk);

    // Apply initial value and start the initialization process
    cb_clk.start <= 1;
    $display(
        "Time: %0t, INFO: test_InitializeRamWithInitialValue - Driving initial_value=0x%h, start=1",
        $time, tb_initial_value);

    // Loop through each address and verify initialization
    for (i = 0; i < Depth; i++) begin
      @(cb_clk);
      cb_clk.start <= 0;

      // Check busy, wr_valid, wr_addr, and wr_data
      if (busy !== 1 || wr_valid !== 1 || wr_addr !== expected_wr_addr || wr_data !== expected_wr_data) begin
        $display(
            "Time: %0t, ERROR: test_InitializeRamWithInitialValue - Check failed. Expected busy=1, wr_valid=1, wr_addr=0x%h, wr_data=0x%h, got busy=%b, wr_valid=%b, wr_addr=0x%h, wr_data=0x%h",
            $time, expected_wr_addr, expected_wr_data, busy, wr_valid, wr_addr, wr_data);
        errors++;
      end else begin
        $display(
            "Time: %0t, INFO: test_InitializeRamWithInitialValue - Check passed. Expected busy=1, wr_valid=1, wr_addr=0x%h, wr_data=0x%h is the same as the observed values.",
            $time, expected_wr_addr, expected_wr_data);
      end

      // Increment expected address
      expected_wr_addr++;
    end

    // Wait for busy to be deasserted
    @(cb_clk);
    if (busy !== 0) begin
      $display(
          "Time: %0t, ERROR: test_InitializeRamWithInitialValue - Check failed. Expected busy=0, got busy=%b",
          $time, busy);
      errors++;
    end else begin
      $display(
          "Time: %0t, INFO: test_InitializeRamWithInitialValue - Check passed. Expected busy=0 is the same as the observed value (both are 0).",
          $time);
    end

    // Report test status
    if (errors == 0) begin
      $display("Time: %0t, PASSED: test_InitializeRamWithInitialValue", $time);
    end else begin
      $display("Time: %0t, FAILED: test_InitializeRamWithInitialValue", $time);
      test_failed = 1;
    end
  endtask
endmodule

// verilog_lint: waive-stop line-length
