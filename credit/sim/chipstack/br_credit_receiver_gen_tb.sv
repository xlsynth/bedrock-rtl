//=============================================================
// Testbench for Module: br_credit_receiver
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_credit_receiver
//=============================================================

module br_credit_receiver_gen_tb;
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
  parameter int Width = 1;
  parameter int MaxCredit = 8;
  parameter bit RegisterPushCredit = 0;
  parameter int PopCreditMaxChange = 1;
  localparam int CounterWidth = $clog2((MaxCredit + 1));
  localparam int PopCreditChangeWidth = $clog2((PopCreditMaxChange + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic                            clk;
  logic                            rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic                            push_credit_stall;
  logic                            push_valid;
  logic [               Width-1:0] push_data;
  logic [PopCreditChangeWidth-1:0] pop_credit;
  logic [        CounterWidth-1:0] credit_initial;
  logic [        CounterWidth-1:0] credit_withhold;
  logic                            push_credit;
  logic                            pop_valid;
  logic [               Width-1:0] pop_data;
  logic [        CounterWidth-1:0] credit_count;
  logic [        CounterWidth-1:0] credit_available;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_credit_receiver #(
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPushCredit(RegisterPushCredit),
      .PopCreditMaxChange(PopCreditMaxChange)
  ) dut (
      .clk(clk),
      .rst(rst),
      .push_credit_stall(push_credit_stall),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_credit(pop_credit),
      .credit_initial(credit_initial),
      .credit_withhold(credit_withhold),
      .push_credit(push_credit),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .credit_count(credit_count),
      .credit_available(credit_available)
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
    inout rst, push_credit_stall, push_valid, push_data,
    pop_credit, credit_initial, credit_withhold;
    input push_credit, pop_valid, pop_data, credit_count, credit_available;
  endclocking


  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    if (NO_ASSERTS_ON_RESET) $assertoff;
    #(TIMEOUT);
    $display({"Error: Testbench timeout!"});
    $finish;
  end

  //===========================================================
  // Reset Generation
  //===========================================================
  task automatic reset_dut;
    if (NO_ASSERTS_ON_RESET) $assertoff;
    // Set all the DUT inputs to zero, making sure there are no X/Z at the inputs.
    cb_clk.push_credit_stall <= 'h0;
    cb_clk.push_valid <= 'h0;
    cb_clk.push_data <= 'h0;
    cb_clk.pop_credit <= 'h0;
    cb_clk.credit_initial <= 'h4;
    cb_clk.credit_withhold <= 'h0;

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
    test_PushCreditManagementTransaction1();

    reset_dut();
    test_PopCreditManagementTransaction1();

    $finish;
  end


  task automatic test_PushCreditManagementTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushCreditManagementTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: To verify the push credit management functionality by ensuring credits are available for data transmission.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_push_data;
        logic [CounterWidth-1:0] initial_credit;
        logic [CounterWidth-1:0] expected_credit_count;
        logic [CounterWidth-1:0] expected_credit_available;

        // Preconditions: Initialize credits
        initial_credit = cb_clk.credit_initial;
        @(cb_clk);
        cb_clk.credit_initial  <= initial_credit;
        cb_clk.credit_withhold <= 0;
        @(cb_clk);

        // Step 1: Set `push_valid` to indicate a push operation request
        cb_clk.push_valid <= 1;
        random_push_data = $urandom();
        cb_clk.push_data <= random_push_data;
        @(cb_clk);
        $display({"Time: %0t, INFO: test_PushCreditManagementTransaction1 - Driving push_valid=1,",
                  "push_data=0x%h"}, $time, random_push_data);

        // Step 2: Monitor `credit_available` to ensure sufficient credits for the push operation
        expected_credit_available = initial_credit;
        if (cb_clk.credit_available != expected_credit_available) begin
          $display({"Time: %0t, ERROR: test_PushCreditManagementTransaction1 - Check failed.",
                    "Expected credit_available=%0d, got %0d"}, $time, expected_credit_available,
                     credit_available);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushCreditManagementTransaction1 - Check passed.",
                    "Expected credit_available=%0d is the same as the observed value."}, $time,
                     expected_credit_available);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 3: If credits are available, expect `push_credit` to be asserted
        if (cb_clk.push_credit !== 1) begin
          $display({"Time: %0t, ERROR: test_PushCreditManagementTransaction1 - Check failed.",
                    "Expected push_credit=1, got %0d"}, $time, push_credit);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushCreditManagementTransaction1 - Check passed.",
                    "push_credit is asserted as expected."}, $time);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 4: Verify that `credit_count` is updated to reflect the new credit state after the push
        expected_credit_count = initial_credit - 1;
        if (cb_clk.credit_count != expected_credit_count) begin
          $display({"Time: %0t, ERROR: test_PushCreditManagementTransaction1 - Check failed.",
                    "Expected credit_count=%0d, got %0d"}, $time, expected_credit_count,
                     credit_count);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushCreditManagementTransaction1 - Check passed.",
                    "Expected credit_count=%0d is the same as the observed value."}, $time,
                     expected_credit_count);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 5: Confirm that `credit_available` is updated to reflect the remaining available credits
        expected_credit_available = expected_credit_count;
        if (cb_clk.credit_available != expected_credit_available) begin
          $display({"Time: %0t, ERROR: test_PushCreditManagementTransaction1 - Check failed.",
                    "Expected credit_available=%0d, got %0d"}, $time, expected_credit_available,
                     credit_available);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushCreditManagementTransaction1 - Check passed.",
                    "Expected credit_available=%0d is the same as the observed value."}, $time,
                     expected_credit_available);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushCreditManagementTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushCreditManagementTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopCreditManagementTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopCreditManagementTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: To verify the pop credit management functionality by ensuring credits are correctly decremented when data is received.

        // Local variables declaration
        int test_failed = -1;
        logic [CounterWidth-1:0] initial_credit_count;
        logic [CounterWidth-1:0] expected_credit_count;
        logic [CounterWidth-1:0] expected_credit_available;
        logic [Width-1:0] expected_pop_data;
        logic [PopCreditChangeWidth-1:0] pop_credit_value;

        // Initialize the test environment
        initial_credit_count = cb_clk.credit_initial;
        pop_credit_value = $urandom_range(1, PopCreditMaxChange);
        expected_credit_count = initial_credit_count - pop_credit_value;
        expected_credit_available = expected_credit_count;
        expected_pop_data = $urandom();

        // Apply initial conditions
        @(cb_clk);
        cb_clk.pop_credit <= pop_credit_value;
        cb_clk.push_valid <= 1;
        cb_clk.push_data <= expected_pop_data;
        cb_clk.credit_withhold <= 0;

        // Wait for the system to stabilize
        @(cb_clk);

        // Step 1: Set `pop_credit` to indicate a pop operation request
        $display({"Time: %0t, INFO: test_PopCreditManagementTransaction1 - Driving pop_credit=0x%h"
                   }, $time, pop_credit_value);

        // Step 2: Monitor `credit_available` to ensure sufficient credits for the pop operation
        if (cb_clk.credit_available < pop_credit_value) begin
          $display({"Time: %0t, ERROR: test_PopCreditManagementTransaction1 - Insufficient credits",
                    "for pop operation.", "Available: %0d, Required: %0d"}, $time,
                     credit_available, pop_credit_value);
          test_failed = 1;
        end else begin
          // Step 3: If credits are sufficient, expect `pop_valid` to be asserted
          if (!cb_clk.pop_valid) begin
            $display(
                {"Time: %0t, ERROR: test_PopCreditManagementTransaction1 - pop_valid not asserted",
                 "as expected."}, $time);
            test_failed = 1;
          end else begin
            $display(
                {"Time: %0t, INFO: test_PopCreditManagementTransaction1 - pop_valid asserted as",
                 "expected."}, $time);
          end

          // Step 4: Verify that the data on `pop_data` corresponds to the popped credits
          if (cb_clk.pop_data !== expected_pop_data) begin
            $display({"Time: %0t, ERROR: test_PopCreditManagementTransaction1 - pop_data mismatch.",
                      "Expected: 0x%h, Got: 0x%h"}, $time, expected_pop_data, pop_data);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PopCreditManagementTransaction1 - pop_data matches",
                      "expected value."}, $time);
          end

          // Step 5: Confirm that `credit_count` is updated to reflect the new credit state after the pop
          if (cb_clk.credit_count !== expected_credit_count) begin
            $display(
                {"Time: %0t, ERROR: test_PopCreditManagementTransaction1 - credit_count mismatch.",
                 "Expected: %0d, Got: %0d"}, $time, expected_credit_count, credit_count);
            test_failed = 1;
          end else begin
            $display(
                {"Time: %0t, INFO: test_PopCreditManagementTransaction1 - credit_count updated",
                 "correctly."}, $time);
          end

          // Step 6: Ensure `credit_available` is updated to reflect the remaining available credits
          if (cb_clk.credit_available !== expected_credit_available) begin
            $display({"Time: %0t, ERROR: test_PopCreditManagementTransaction1 - credit_available",
                      "mismatch.", "Expected: %0d, Got: %0d"}, $time, expected_credit_available,
                       credit_available);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PopCreditManagementTransaction1 - credit_available",
                      "updated correctly."}, $time);
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopCreditManagementTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopCreditManagementTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
