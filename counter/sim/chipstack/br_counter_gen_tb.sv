//=============================================================
// Testbench for Module: br_counter
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_counter
//=============================================================

module br_counter_gen_tb;
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
  parameter int MaxChange = 1;
  parameter bit EnableWrap = 1;
  localparam int ValueWidth = $clog2((MaxValue + 1));
  localparam int ChangeWidth = $clog2((MaxChange + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic reinit;
  logic [ValueWidth-1:0] initial_value;
  logic incr_valid;
  logic [ChangeWidth-1:0] incr;
  logic decr_valid;
  logic [ChangeWidth-1:0] decr;
  logic [ValueWidth-1:0] value;
  logic [ValueWidth-1:0] value_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_counter #(
      .MaxValue  (MaxValue),
      .MaxChange (MaxChange),
      .EnableWrap(EnableWrap)
  ) dut (
      .clk(clk),
      .rst(rst),
      .reinit(reinit),
      .initial_value(initial_value),
      .incr_valid(incr_valid),
      .incr(incr),
      .decr_valid(decr_valid),
      .decr(decr),
      .value(value),
      .value_next(value_next)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1; // If any test fails, set this flag to 0.

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, reinit, initial_value, incr_valid, incr, decr_valid, decr;
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
    cb_clk.decr_valid <= 'h0;
    cb_clk.decr <= 'h0;

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
    test_IncrementOperation();

    reset_dut();
    test_DecrementOperation();

    reset_dut();
    test_SimultaneousIncrementAndDecrement();

    reset_dut();
    test_ReinitializationWithChange();

    if (overall_tb_status == 'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_IncrementOperation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_IncrementOperation. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: Verify the increment operation of the counter.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value;
        logic [ValueWidth-1:0] observed_value_next;
        logic [ValueWidth-1:0] observed_value;
        logic [ChangeWidth-1:0] increment_value;

        // Initialize the increment value
        increment_value = $urandom_range(0, MaxChange);

        // Wait for a clock cycle to ensure proper stimulus propagation
        @(cb_clk);

        // Step 1: Assert `incr_valid` to indicate a valid increment operation
        cb_clk.incr_valid <= 1;
        cb_clk.incr <= increment_value;
        $display($sformatf({"Time: %0t, INFO: test_IncrementOperation - Driving incr_valid=1, incr=0x%h"},
                   $time, increment_value));

        // Step 2: Provide the increment amount on `incr`
        expected_value = cb_clk.value + increment_value;

        // Wait for a clock cycle to observe the next value
        @(cb_clk);

        // Step 3: Observe that the design calculates the next counter value and updates `value_next`
        observed_value_next = cb_clk.value_next;
        if (observed_value_next !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_IncrementOperation - Check failed. ",
                    "Expected value_next=0x%h, got 0x%h"}, $time, expected_value,
                     observed_value_next));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_IncrementOperation - Check passed. ",
                    "Expected value_next=0x%h, observed value_next=0x%h"}, $time, expected_value,
                     observed_value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Step 4: On the next clock cycle, verify that the design updates `value` to the new counter value
        @(cb_clk);
        observed_value = cb_clk.value;
        if (observed_value !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_IncrementOperation - Check failed. ",
                    "Expected value=0x%h, got 0x%h"}, $time, expected_value, observed_value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_IncrementOperation - Check passed. ",
                    "Expected value=0x%h, observed value=0x%h"}, $time, expected_value,
                     observed_value));
          if (test_failed != 1) test_failed = 0;
        end

        // Reset the increment valid signal
        cb_clk.incr_valid <= 0;

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_IncrementOperation", $time);
        end else begin
          $display("Time: %0t, FAILED: test_IncrementOperation", $time);
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_DecrementOperation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_DecrementOperation. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: Verify the decrement operation of the counter.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value;
        logic [ValueWidth-1:0] observed_value_next;
        logic [ValueWidth-1:0] observed_value;
        logic [ChangeWidth-1:0] decrement_amount;

        // Initialize the decrement amount with a random value within the allowed range
        decrement_amount = $urandom_range(0, MaxChange);

        // Wait for a clock cycle to ensure proper stimulus propagation
        @(cb_clk);

        // Step 1: Assert `decr_valid` to indicate a valid decrement operation
        cb_clk.decr_valid <= 1;
        cb_clk.decr <= decrement_amount;
        $display("Time: %0t, INFO: test_DecrementOperation - Driving decr_valid=1, decr=0x%h",
                   $time, decrement_amount);

        // Step 2: Calculate the expected next value
        expected_value = cb_clk.value - decrement_amount;
        if (EnableWrap && expected_value > MaxValue) begin
          expected_value = expected_value + MaxValue + 1;
        end

        // Wait for a clock cycle to observe the next value
        @(cb_clk);

        // Step 3: Observe that the design calculates the next counter value and updates `value_next`
        observed_value_next = cb_clk.value_next;
        if (observed_value_next !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementOperation - Check failed. ",
                    "Expected value_next=0x%h, got 0x%h"}, $time, expected_value,
                     observed_value_next));
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_DecrementOperation - Check passed. ",
               "Expected value_next=0x%h is the same as the observed value_next (both are 0x%h)."},
                $time, expected_value, observed_value_next);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 4: On the next clock cycle, verify that the design updates `value` to the new counter value
        @(cb_clk);
        observed_value = cb_clk.value;
        if (observed_value !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementOperation - Check failed. ",
                    "Expected value=0x%h, got 0x%h"}, $time, expected_value, observed_value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_DecrementOperation - Check passed. ",
                    "Expected value=0x%h is the same as the observed value (both are 0x%h)."},
                     $time, expected_value, observed_value));
          if (test_failed != 1) test_failed = 0;
        end

        // Reset the decrement signals
        cb_clk.decr_valid <= 0;
        cb_clk.decr <= 0;

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_DecrementOperation", $time);
        end else begin
          $display("Time: %0t, FAILED: test_DecrementOperation", $time);
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_SimultaneousIncrementAndDecrement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_SimultaneousIncrementAndDecrement. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: Verify the counter's behavior when both increment and decrement operations are valid simultaneously.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] expected_value;
        logic [ChangeWidth-1:0] incr_value;
        logic [ChangeWidth-1:0] decr_value;
        logic [ValueWidth-1:0] initial_counter_value;

        // Precondition: Initialize the counter to a known state
        initial_counter_value = $urandom_range(0, MaxValue);  // Example initial cb_clk.value
        incr_value = $urandom_range(0, MaxChange);  // Example increment cb_clk.value
        decr_value = $urandom_range(0, incr_value);  // Example decrement cb_clk.value

        // Apply initial conditions
        @(cb_clk);
        cb_clk.reinit <= 1;
        cb_clk.initial_value <= initial_counter_value;
        cb_clk.incr_valid <= 0;
        cb_clk.decr_valid <= 0;
        $display($sformatf({"Time: %0t, INFO: test_SimultaneousIncrementAndDecrement - Initializing counter ",
                  "to %0d"}, $time, initial_counter_value));

        @(cb_clk);
        cb_clk.reinit <= 0;

        // Step 1: Assert both `incr_valid` and `decr_valid` to indicate simultaneous operations
        @(cb_clk);
        cb_clk.incr_valid <= 1;
        cb_clk.decr_valid <= 1;
        cb_clk.incr <= incr_value;
        cb_clk.decr <= decr_value;
        $display($sformatf({"Time: %0t, INFO: test_SimultaneousIncrementAndDecrement - Driving incr_valid=1, ",
             "decr_valid=1, incr=0x%h, decr=0x%h"}, $time, incr_value, decr_value));

        // Calculate expected value_next
        expected_value_next = initial_counter_value + incr_value - decr_value;

        // Step 2: Observe that the design calculates the net change and updates `value_next`
        @(cb_clk);
        if (cb_clk.value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_SimultaneousIncrementAndDecrement - Check failed. ",
                    "Expected value_next=0x%h, got 0x%h"}, $time, expected_value_next, value_next));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_SimultaneousIncrementAndDecrement - Check passed. ",
                    "Expected value_next=0x%h is the same as the observed value_next"}, $time,
                     expected_value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Step 3: On the next clock cycle, verify that the design updates `value` to reflect the new counter value
        @(cb_clk);
        expected_value = expected_value_next;
        if (cb_clk.value !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_SimultaneousIncrementAndDecrement - Check failed. ",
                    "Expected value=0x%h, got 0x%h"}, $time, expected_value, value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_SimultaneousIncrementAndDecrement - Check passed. ",
                    "Expected value=0x%h is the same as the observed value"}, $time,
                     expected_value));
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_SimultaneousIncrementAndDecrement"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_SimultaneousIncrementAndDecrement"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_ReinitializationWithChange;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_ReinitializationWithChange. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: Verify the counter's reinitialization to a specified initial value while applying an increment or decrement operation in the same cycle.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;

        // Initialize variables
        cb_clk.initial_value <= $urandom_range(0, MaxValue);
        cb_clk.incr <= $urandom_range(0, MaxChange);
        cb_clk.decr <= $urandom_range(0, MaxChange);
        cb_clk.incr_valid <= $urandom() % 2;
        cb_clk.decr_valid <= $urandom() % 2;
        cb_clk.reinit <= 1;

        // Calculate expected value_next
        expected_value_next = cb_clk.initial_value;
        if (cb_clk.incr_valid && cb_clk.decr_valid) begin
          expected_value_next = cb_clk.initial_value + cb_clk.incr - cb_clk.decr;
        end else if (cb_clk.incr_valid) begin
          expected_value_next = cb_clk.initial_value + cb_clk.incr;
        end else if (cb_clk.decr_valid) begin
          expected_value_next = cb_clk.initial_value - cb_clk.decr;
        end

        // Apply stimulus
        @(cb_clk);
        cb_clk.reinit <= reinit;
        cb_clk.initial_value <= initial_value;
        cb_clk.incr_valid <= incr_valid;
        cb_clk.incr <= incr;
        cb_clk.decr_valid <= decr_valid;
        cb_clk.decr <= decr;
        $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithChange - Driving reinit=0x%h, ",
                  "initial_value=0x%h, incr_valid=0x%h, incr=0x%h, decr_valid=0x%h, decr=0x%h"},
                   $time, reinit, initial_value, incr_valid, incr, decr_valid, decr));

        // Wait for the next clock cycle to observe value_next
        @(cb_clk);
        if (cb_clk.value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithChange - Check failed. ",
                    "Expected value_next=0x%h, got value_next=0x%h"}, $time, expected_value_next,
                     value_next));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithChange - Check passed. ",
                    "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                     $time, expected_value_next, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Verify that value updates correctly in the next cycle
        @(cb_clk);
        if (cb_clk.value !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithChange - Check failed. ",
                    "Expected value=0x%h, got value=0x%h"}, $time, expected_value_next, value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithChange - Check passed. ",
                    "Expected value=0x%h is the same as the observed value=0x%h."}, $time,
                     expected_value_next, value));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_ReinitializationWithChange"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_ReinitializationWithChange"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
