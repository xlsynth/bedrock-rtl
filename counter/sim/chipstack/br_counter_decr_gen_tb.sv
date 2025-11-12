// SPDX-License-Identifier: Apache-2.0


module br_counter_decr_gen_tb;
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

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int MaxValue = 1;
  parameter int MaxDecrement = 1;
  localparam int ValueWidth = $clog2((MaxValue + 1));
  localparam int DecrementWidth = $clog2((MaxDecrement + 1));

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
  logic                      decr_valid;
  logic [DecrementWidth-1:0] decr;
  logic [    ValueWidth-1:0] value;
  logic [    ValueWidth-1:0] value_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_counter_decr #(
      .MaxValue(MaxValue),
      .MaxDecrement(MaxDecrement)
  ) dut (
      .clk(clk),
      .rst(rst),
      .reinit(reinit),
      .initial_value(initial_value),
      .decr_valid(decr_valid),
      .decr(decr),
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
    inout rst, reinit, initial_value, decr_valid, decr;
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
    test_DecrementOperation();

    reset_dut();
    test_DecrementWithUnderflowHandling();

    reset_dut();
    test_ReinitializationWithDecrement();

    reset_dut();
    test_ReinitializationWithoutDecrement();

    if (overall_tb_status == 'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_DecrementOperation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_DecrementOperation. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: To verify the decrement operation of the counter.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] current_value;
        logic [ValueWidth-1:0] expected_value_next;
        logic [DecrementWidth-1:0] decrement_value;

        // Initialize the counter to a known state
        decrement_value =
            $urandom_range(1, MaxDecrement);  // Random decrement cb_clk.value within range
        current_value = $urandom_range(0, MaxValue);  // Random initial cb_clk.value within range
        cb_clk.initial_value <= current_value;
        cb_clk.reinit <= 1;
        @(cb_clk);
        cb_clk.reinit <= 0;
        @(cb_clk);

        // Apply decrement operation
        cb_clk.decr <= decrement_value;
        cb_clk.decr_valid <= 1;

        // Calculate expected value_next
        expected_value_next = (current_value >= decrement_value) ?
                                (current_value - decrement_value) :
                                (MaxValue + 1 - (decrement_value - current_value));

        // Check if value_next is as expected
        if (cb_clk.value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementOperation - Check failed. ",
                              "current_value=0x%h, decrement_value=0x%h ,",
                              "expected value_next: 0x%h, got: 0x%h"}, $time, current_value,
                               decrement_value, expected_value_next, cb_clk.value_next));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_DecrementOperation - Check passed. ",
                              "Expected value_next: 0x%h is the same as the observed value_next."},
                               $time, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        @(cb_clk);
        cb_clk.decr_valid <= 0;

        // Wait for the next clock cycle to check the updated value
        @(cb_clk);

        // Check if value is updated with value_next
        if (cb_clk.value !== cb_clk.value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementOperation - Check failed. ",
                              "Expected value: 0x%h, got: 0x%h"}, $time, value_next, value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_DecrementOperation - Check passed. ",
                              "Expected value: 0x%h is the same as the observed value."}, $time,
                               value));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_DecrementOperation"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_DecrementOperation"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_DecrementWithUnderflowHandling;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_DecrementWithUnderflowHandling. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: To verify the decrement operation with underflow handling.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] current_value;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] expected_value;
        logic [DecrementWidth-1:0] decrement_value;

        // Initialize the counter to a known value
        current_value   = $urandom_range(1, MaxValue);
        decrement_value = $urandom_range(1, current_value) - 1;

        // Apply initial conditions
        @(cb_clk);
        cb_clk.reinit <= 1;
        cb_clk.initial_value <= current_value;
        cb_clk.decr_valid <= 0;
        cb_clk.decr <= 0;
        @(cb_clk);
        cb_clk.reinit <= 0;

        // Apply decrement to cause underflow
        @(cb_clk);
        cb_clk.decr_valid <= 1;
        cb_clk.decr <= decrement_value;
        $display($sformatf({"Time: %0t, INFO: test_DecrementWithUnderflowHandling - ",
                            "Driving decr_valid=1, decr=0x%h"}, $time, decrement_value));

        // Calculate expected wrapped-around value
        expected_value_next = (current_value - decrement_value) + (MaxValue + 1);

        // Check value_next
        @(cb_clk);
        if (cb_clk.value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementWithUnderflowHandling - ",
                              "Check failed. Expected value_next=0x%h, got 0x%h"}, $time,
                               expected_value_next, value_next));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_DecrementWithUnderflowHandling - ", "Check passed. ",
                        "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                         $time, expected_value_next, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Check value update in the next cycle
        expected_value = expected_value_next;
        @(cb_clk);
        if (cb_clk.value !== expected_value) begin
          $display($sformatf({"Time: %0t, ERROR: test_DecrementWithUnderflowHandling - ",
                              "Check failed. ", "Expected value=0x%h, got 0x%h"}, $time,
                               expected_value, value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_DecrementWithUnderflowHandling - ",
                              "Check passed. ",
                              "Expected value=0x%h is the same as the observed value=0x%h."},
                               $time, expected_value, value));
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_DecrementWithUnderflowHandling"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_DecrementWithUnderflowHandling"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_ReinitializationWithDecrement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_ReinitializationWithDecrement. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: To verify reinitialization of the counter with a decrement in the same cycle.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] observed_value_next;
        logic [ValueWidth-1:0] observed_value;

        // Initialize inputs
        logic [ValueWidth-1:0] initial_value = $urandom_range(0, MaxValue);
        logic [DecrementWidth-1:0] decr = $urandom_range(1, initial_value) - 1;

        // Apply stimulus
        @(cb_clk);
        cb_clk.reinit <= 1;
        cb_clk.initial_value <= initial_value;
        cb_clk.decr_valid <= 1;
        cb_clk.decr <= decr;
        $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithDecrement - ",
                            "Driving reinit=1, ", "initial_value=0x%h, decr_valid=1, decr=0x%h"},
                             $time, initial_value, decr));

        // Calculate expected value_next
        expected_value_next = cb_clk.initial_value - cb_clk.decr;

        // Wait for the next clock cycle to observe the results

        observed_value_next = cb_clk.value_next;
        observed_value = cb_clk.value;

        // Check if value_next is as expected
        if (observed_value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithDecrement - ",
                              "Check failed. ", "Expected value_next=0x%h, got value_next=0x%h"},
                               $time, expected_value_next, observed_value_next));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_ReinitializationWithDecrement -", " Check passed. ",
                        "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                         $time, expected_value_next, observed_value_next));
          if (test_failed != 1) test_failed = 0;
        end

        @(cb_clk);
        // Check if value is updated to value_next
        if (observed_value !== observed_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithDecrement - ",
                              "Check failed. ", "Expected value=0x%h, got value=0x%h"}, $time,
                               observed_value_next, observed_value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithDecrement - ",
                              "Check passed. ",
                              "Expected value=0x%h is the same as the observed value=0x%h."},
                               $time, observed_value_next, observed_value));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_ReinitializationWithDecrement"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_ReinitializationWithDecrement"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_ReinitializationWithoutDecrement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_ReinitializationWithoutDecrement. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 0;
      end
      begin
        // Purpose: To verify reinitialization of the counter without applying any decrement.
        // Local variables declaration
        int test_failed = -1;
        logic [ValueWidth-1:0] expected_value_next;
        logic [ValueWidth-1:0] initial_value_random;

        // Generate a random initial value within the valid range
        initial_value_random = $urandom_range(0, MaxValue);

        // Apply stimulus
        @(cb_clk);
        cb_clk.reinit <= 1;
        cb_clk.initial_value <= initial_value_random;
        cb_clk.decr_valid <= 0;
        cb_clk.decr <= 0;  // No decrement

        // Display the applied stimulus
        $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithoutDecrement - ",
                            "Driving reinit=1, ", "initial_value=0x%h, decr_valid=0, decr=0"},
                             $time, initial_value_random));

        // Calculate expected value_next
        expected_value_next = initial_value_random;

        // Wait for the next clock cycle to check the results
        @(cb_clk);

        // Check if value_next is set to initial_value
        if (cb_clk.value_next !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithoutDecrement - ",
                              "Check failed. ", "Expected value_next=0x%h, got 0x%h"}, $time,
                               expected_value_next, value_next));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_ReinitializationWithoutDecrement - ",
                        "Check passed. ",
                        "Expected value_next=0x%h is the same as the observed value_next=0x%h."},
                         $time, expected_value_next, value_next));
          if (test_failed != 1) test_failed = 0;
        end

        // Wait for the next clock cycle to check if value is updated to value_next
        @(cb_clk);

        // Check if value is updated to value_next
        if (cb_clk.value !== expected_value_next) begin
          $display($sformatf({"Time: %0t, ERROR: test_ReinitializationWithoutDecrement - ",
                              "Check failed. ", "Expected value=0x%h, got 0x%h"}, $time,
                               expected_value_next, value));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_ReinitializationWithoutDecrement - ",
                              "Check passed. ",
                              "Expected value=0x%h is the same as the observed value=0x%h."},
                               $time, expected_value_next, value));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_ReinitializationWithoutDecrement"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_ReinitializationWithoutDecrement"}, $time));
          overall_tb_status = 0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
