//=============================================================
// Testbench for Module: br_counter_incr
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_counter_incr
//=============================================================

module br_counter_incr_gen_tb;
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
  parameter int NO_ASSERTS_ON_RESET = 0;  // Disable assertions during reset

  //===========================================================
  // DUT Imports and Includes
  //===========================================================

  `include "br_asserts_internal.svh"
  `include "br_registers.svh"
  `include "br_unused.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int MaxValue = 1;
  parameter int MaxIncrement = 1;
  localparam int ValueWidth = $clog2((MaxValue + 1));
  localparam int IncrementWidth = $clog2((MaxIncrement + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic                      clk;
  logic                      rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic                      reinit;
  logic [    ValueWidth-1:0] initial_value;
  logic                      incr_valid;
  logic [IncrementWidth-1:0] incr;
  logic [    ValueWidth-1:0] value;
  logic [    ValueWidth-1:0] value_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_counter_incr #(
      .MaxValue(MaxValue),
      .MaxIncrement(MaxIncrement)
  ) dut (
      .clk(clk),
      .rst(rst),
      .reinit(reinit),
      .initial_value(initial_value),
      .incr_valid(incr_valid),
      .incr(incr),
      .value(value),
      .value_next(value_next)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;  // If any test fails, set this flag to 0.

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, reinit, initial_value, incr_valid, incr;
    input value, value_next;
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
    cb_clk.reinit <= 'h0;
    cb_clk.initial_value <= 'h0;
    cb_clk.incr_valid <= 'h0;
    cb_clk.incr <= 'h0;

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
    test_IncrementCounterTransaction1();

    reset_dut();
    test_OverflowHandlingTransaction1();

    reset_dut();
    test_OverflowHandlingTransaction2();

    reset_dut();
    test_CounterReinitializationTransaction1();

    if (overall_tb_status == 'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_IncrementCounterTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_IncrementCounterTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // This task tests the increment functionality of the br_counter_incr module.
        // It verifies that the counter increments correctly when incr_valid is asserted.

        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value;
        logic [ValueWidth-1:0] current_value;
        logic [IncrementWidth-1:0] random_incr;
        int i;

        // Initial setup
        expected_value = 0;
        current_value  = 0;

        // Wait for a clock cycle to ensure proper setup
        @(cb_clk);

        // Test loop for multiple increments
        for (i = 0; i < 10; i++) begin
          // Generate a random increment value within the allowed range
          random_incr = $urandom_range(0, MaxIncrement);

          // Apply stimulus
          cb_clk.incr <= random_incr;
          cb_clk.incr_valid <= 1;
          @(cb_clk);
          cb_clk.incr_valid <= 0;
          $display($sformatf(
                       {"Time: %0t, INFO: test_IncrementCounterTransaction1 - Driving incr=0x%h, ",
                        "incr_valid=1"}, $time, random_incr));

          // Calculate expected value considering overflow
          expected_value = (current_value + random_incr) % (MaxValue + 1);

          // Wait for the next clock cycle
          @(cb_clk);

          // Capture the current value from the DUT
          current_value = cb_clk.value;

          // Check if the expected value matches the current value
          if (current_value !== expected_value) begin
            $display($sformatf(
                         {"Time: %0t, ERROR: test_IncrementCounterTransaction1 - Check failed. ",
                          "Expected value=0x%h, got value=0x%h"}, $time, expected_value,
                           current_value));
            test_failed = 1;
          end else begin
            $display($sformatf(
                         {"Time: %0t, INFO: test_IncrementCounterTransaction1 - Check passed. ",
                          "Expected value=0x%h is the same as the observed value=0x%h."}, $time,
                           expected_value, current_value));
            if (test_failed != 1) test_failed = 0;
          end

          // Disable further stimulus application in the next cycle
          cb_clk.incr_valid <= 0;
          @(cb_clk);
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_IncrementCounterTransaction1"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_IncrementCounterTransaction1"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_OverflowHandlingTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_OverflowHandlingTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: Test the overflow handling of the counter when the sum of the current value and increment exceeds MaxValue.

        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] observed_value_next;

        // Preconditions
        cb_clk.initial_value <= MaxValue - 1;  // Set cb_clk.initial_value close to MaxValue
        cb_clk.incr <= MaxIncrement;
        // Set cb_clk.incr such that cb_clk.value + cb_clk.incr > MaxValue

        // Apply stimulus
        @(cb_clk);
        cb_clk.reinit <= 1;
        cb_clk.initial_value <= cb_clk.initial_value;
        cb_clk.incr_valid <= 1;
        cb_clk.incr <= cb_clk.incr;
        @(cb_clk);
        cb_clk.reinit <= 0;

        // Calculate expected value_next
        expected_value_next = (cb_clk.initial_value + cb_clk.incr) % (MaxValue + 1);

        // Monitor and check value_next
        @(cb_clk);
        observed_value_next = cb_clk.value_next;
        if (observed_value_next !== expected_value_next) begin
          $display($sformatf(
                       {"Time: %0t, ERROR: test_OverflowHandlingTransaction1 - Check failed. ",
                        "Expected value_next=0x%h, got 0x%h"}, $time, expected_value_next,
                         observed_value_next));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_OverflowHandlingTransaction1 - Check passed. ",
                        "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                         $time, expected_value_next, observed_value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_OverflowHandlingTransaction1"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_OverflowHandlingTransaction1"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_OverflowHandlingTransaction2;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_OverflowHandlingTransaction2. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // This task tests the overflow handling of the br_counter_incr module by setting the counter to MaxValue and incrementing by 1, expecting a wrap-around to 0.

        // Local variables declaration
        int test_failed = -1;
        logic [3:0] value_next_expected;

        // Preconditions
        cb_clk.initial_value <= MaxValue;
        cb_clk.incr_valid <= 1;
        cb_clk.incr <= MaxIncrement;
        value_next_expected = 0;

        // Apply stimulus
        @(cb_clk);
        cb_clk.initial_value <= initial_value;
        cb_clk.incr_valid <= incr_valid;
        cb_clk.incr <= incr;
        $display($sformatf({"Time: %0t, INFO: test_OverflowHandlingTransaction2 - Driving ",
                            "initial_value=0x%h, incr_valid=%b, incr=0x%h"}, $time, initial_value,
                             incr_valid, incr));

        // Wait for the next clock cycle to observe value_next
        @(cb_clk);

        // Check the result
        if (cb_clk.value_next !== value_next_expected) begin
          $display($sformatf(
                       {"Time: %0t, ERROR: test_OverflowHandlingTransaction2 - Check failed. ",
                        "Expected value_next=0x%h, got 0x%h"}, $time, value_next_expected,
                         value_next));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_OverflowHandlingTransaction2 - Check passed. ",
                        "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                         $time, value_next_expected, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_OverflowHandlingTransaction2"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_OverflowHandlingTransaction2"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CounterReinitializationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_CounterReinitializationTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // This task tests the counter reinitialization functionality, ensuring that the counter is correctly set to the initial value and optionally incremented in the same cycle.

        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] expected_value;
        logic [ValueWidth-1:0] random_initial_value;
        logic [IncrementWidth-1:0] random_incr;
        logic random_incr_valid;

        // Precondition: Set initial values
        random_initial_value = $urandom_range(0, MaxValue);
        random_incr = $urandom_range(0, MaxIncrement);
        random_incr_valid = $urandom() % 2;

        // Apply stimulus
        @(cb_clk);
        cb_clk.initial_value <= random_initial_value;
        cb_clk.reinit <= 1;
        cb_clk.incr_valid <= random_incr_valid;
        cb_clk.incr <= random_incr;
        $display($sformatf({"Time: %0t, INFO: test_CounterReinitializationTransaction1 - Driving ",
                            "initial_value=0x%h, reinit=1, incr_valid=%0b, incr=0x%h"}, $time,
                             random_initial_value, random_incr_valid, random_incr));

        // Calculate expected value_next
        if (random_incr_valid) begin
          expected_value_next = (random_initial_value + random_incr) % (MaxValue + 1);
        end else begin
          expected_value_next = random_initial_value;
        end

        // Check value_next
        @(cb_clk);
        if (cb_clk.value_next !== expected_value_next) begin
          $display(
              $sformatf(
                  {"Time: %0t, ERROR: test_CounterReinitializationTransaction1 - Check failed. ",
                   "Expected value_next=0x%h, got 0x%h"}, $time, expected_value_next, value_next));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_CounterReinitializationTransaction1 - Check passed. ",
                   "Expected value_next=0x%h is the same as the observed value_next=0x%h."}, $time,
                    expected_value_next, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Check value on the next cycle
        @(cb_clk);
        expected_value = expected_value_next;
        if (cb_clk.value !== expected_value) begin
          $display(
              $sformatf(
                  {"Time: %0t, ERROR: test_CounterReinitializationTransaction1 - Check failed. ",
                   "Expected value=0x%h, got 0x%h"}, $time, expected_value, value));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_CounterReinitializationTransaction1 - Check passed. ",
                   "Expected value=0x%h is the same as the observed value=0x%h."}, $time,
                    expected_value, value));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_CounterReinitializationTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_CounterReinitializationTransaction1", $time);
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
