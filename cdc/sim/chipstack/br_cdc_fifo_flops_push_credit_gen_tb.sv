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

module br_cdc_fifo_flops_push_credit_gen_tb;
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
  // DUT Parameters
  //===========================================================
  parameter int Depth = 2;
  parameter int Width = 1;
  parameter int MaxCredit = Depth;
  parameter bit RegisterPopOutputs = 1;
  parameter int NumSyncStages = 3;
  parameter int FlopRamDepthTiles = 1;
  parameter int FlopRamWidthTiles = 1;
  parameter int FlopRamAddressDepthStages = 0;
  parameter int FlopRamReadDataDepthStages = 0;
  parameter int FlopRamReadDataWidthStages = 0;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2((Depth + 1));
  localparam int CreditWidth = $clog2((MaxCredit + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic push_clk;
  logic pop_clk;
  logic push_rst;
  logic pop_rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic push_credit_stall;
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic [CreditWidth-1:0] credit_initial_push;
  logic [CreditWidth-1:0] credit_withhold_push;
  logic push_credit;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic push_full;
  logic [CountWidth-1:0] push_slots;
  logic [CreditWidth-1:0] available;
  logic [CreditWidth-1:0] credit_count_push;
  logic [CreditWidth-1:0] credit_available_push;
  logic pop_empty;
  logic [CountWidth-1:0] pop_items;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_flops_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumSyncStages(NumSyncStages),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages)
  ) dut (
      .push_clk(push_clk),
      .pop_clk(pop_clk),
      .push_rst(push_rst),
      .pop_rst(pop_rst),
      .push_sender_in_reset(1'b0),  // unused
      .push_receiver_in_reset(),  // unused
      .push_credit_stall(push_credit_stall),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .credit_initial_push(credit_initial_push),
      .credit_withhold_push(credit_withhold_push),
      .push_credit(push_credit),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .push_full(push_full),
      .push_slots(push_slots),
      .credit_count_push(credit_count_push),
      .credit_available_push(credit_available_push),
      .pop_empty(pop_empty),
      .pop_items(pop_items)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;

  //===========================================================
  // Clock Generation
  //===========================================================
  assign pop_clk = push_clk;
  initial begin
    push_clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) push_clk = ~push_clk;
  end
  clocking cb_push_clk @(posedge push_clk);
    default input #1step output #4;
    inout push_rst, push_credit_stall, push_valid, push_data,
          credit_initial_push, credit_withhold_push;
    input push_credit, push_full, push_slots, credit_count_push, credit_available_push;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout pop_rst, pop_ready;
    input pop_valid, pop_data, pop_empty, pop_items;
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
    cb_push_clk.push_credit_stall <= 'h0;
    cb_push_clk.push_valid <= 'h0;
    cb_push_clk.push_data <= 'h0;
    cb_pop_clk.pop_ready <= 'h0;
    cb_push_clk.credit_initial_push <= 'h0;
    cb_push_clk.credit_withhold_push <= 'h0;

    // Wiggling the reset signal.
    cb_push_clk.push_rst <= 1'bx;
    cb_pop_clk.pop_rst <= 1'bx;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    cb_push_clk.push_rst <= 1'b1;
    cb_pop_clk.pop_rst   <= 1'b1;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    cb_push_clk.push_rst <= 1'b0;
    cb_pop_clk.pop_rst   <= 1'b0;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    if (NO_ASSERTS_ON_RESET) $asserton;
  endtask

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
    reset_dut();
    test_PushDataOperationTransaction1();

    reset_dut();
    test_PushDataOperationTransaction2();

    reset_dut();
    //test_PopDataOperationTransaction1(); // This is not applicable to this design.

    reset_dut();
    test_CreditInitializationTransaction1();

    reset_dut();
    test_CreditWithholdingTransaction1();

    reset_dut();
    test_CreditAvailabilityMonitoringTransaction1();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_PushDataOperationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_PushDataOperationTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Test the push data operation of the FIFO, ensuring data is pushed only when there is available space.
        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_data;
        logic [CreditWidth-1:0] initial_credit;
        logic [CreditWidth-1:0] withhold_credit;
        logic [CountWidth-1:0] expected_push_slots;

        // Preconditions: Initialize credits and ensure FIFO is not full
        initial_credit = $urandom_range(1, MaxCredit);
        withhold_credit = 0;
        expected_push_slots = Depth;

        // Apply initial credit
        @(cb_push_clk);
        cb_push_clk.credit_initial_push  <= initial_credit;
        cb_push_clk.credit_withhold_push <= withhold_credit;
        $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction1 -  ",
                            "Initial credits set to %0d"}, $time, initial_credit));

        // Wait for a clock cycle to propagate initial conditions
        @(cb_push_clk);

        // Step 1: Assert `push_valid` to indicate valid data on `push_data`
        random_data = $urandom();
        @(cb_push_clk);
        cb_push_clk.push_valid <= 1;
        cb_push_clk.push_data  <= random_data;

        $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction1 -  ",
                            "Driving push_valid=1, ", "push_data=0x%h"}, $time, random_data));

        // Step 2: Monitor `push_full` to check if the FIFO is full
        @(cb_push_clk);
        expected_push_slots -= 1;
        if (cb_push_clk.push_full) begin
          $display($sformatf({"Time: %0t, ERROR: test_PushDataOperationTransaction1 -  ",
                              "FIFO is full, cannot ", "push data"}, $time));
          test_failed = 1;
        end else begin
          // Step 3: If `push_full` is deasserted, acknowledge data push by asserting `push_credit`
          if (cb_push_clk.push_credit) begin
            $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction1 - ",
                                "Data push acknowledged ", "with push_credit=1"}, $time));

          end else begin
            $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction1 - ",
                                "push_credit not asserted"}, $time));
            test_failed = 0;
          end
        end

        // Step 4: Update `push_slots` to reflect current available slots
        @(cb_push_clk);
        if (cb_push_clk.push_slots != expected_push_slots) begin
          $display($sformatf({"Time: %0t, ERROR: test_PushDataOperationTransaction1 -  ",
                              "push_slots mismatch. ", "Expected: %0d, Got: %0d"}, $time,
                               expected_push_slots, cb_push_clk.push_slots));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction1 -  ",
                              "push_slots correctly ", "updated to %0d"}, $time, push_slots));
        end

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_PushDataOperationTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_PushDataOperationTransaction1", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushDataOperationTransaction2;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_PushDataOperationTransaction2. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Simulate a stall condition during the push operation and verify the behavior of the FIFO.

        // Local variables declaration
        int test_failed = -1;
        localparam int CountWidth = $clog2(Depth + 1);
        logic [CountWidth-1:0] initial_push_slots;

        // Precondition: Capture initial state of push_slots
        @(cb_push_clk);
        initial_push_slots = cb_push_clk.push_slots;

        // Step 1: Assert `push_credit_stall` to simulate a stall condition
        cb_push_clk.push_credit_stall <= 1;
        @(cb_push_clk);
        $display(
            $sformatf(
                {"Time: %0t, INFO: test_PushDataOperationTransaction2 - Asserted push_credit_stall"
                  }, $time));

        // Step 2: Deassert `push_credit` to indicate no data can be pushed during the stall
        if (cb_push_clk.push_credit !== 0) begin
          $display(
              $sformatf(
                  {"Time: %0t, ERROR: test_PushDataOperationTransaction2 - push_credit should be ",
                   "deasserted during stall. ", "Expected 0, got %0b"}, $time, push_credit));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_PushDataOperationTransaction2 - push_credit correctly ",
                   "deasserted during stall"}, $time));
          if (test_failed != 1) test_failed = 0;
        end

        // Step 3: Maintain current state of `push_slots` during the stall
        if (cb_push_clk.push_slots !== initial_push_slots) begin
          $display($sformatf({"Time: %0t, ERROR: test_PushDataOperationTransaction2 - push_slots ",
                              "changed during stall.", "Expected %0d, got %0d"}, $time,
                               initial_push_slots, push_slots));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_PushDataOperationTransaction2 - ",
                              "push_slots maintained during stall"}, $time));
          if (test_failed != 1) test_failed = 0;
        end

        // End of test: Report status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_PushDataOperationTransaction2", $time);
        end else begin
          $display("Time: %0t, FAILED: test_PushDataOperationTransaction2", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopDataOperationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_PopDataOperationTransaction1.",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Test the pop data operation, ensuring data is popped only when the FIFO is not empty and the pop interface is ready.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] expected_pop_data;
        logic [CountWidth-1:0] expected_pop_items;

        // Preconditions: Initialize FIFO with known data
        // Assuming FIFO is pre-filled with known data for this test scenario
        expected_pop_data  = 'hA5;  // Example data
        expected_pop_items = 1;  // Assuming 1 item in FIFO

        @(cb_push_clk);
        cb_push_clk.push_valid <= 1;

        // Wait for 6 pop clock
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);

        if (cb_pop_clk.pop_empty == 0) begin
          // Step 2: Monitor cb_pop_clk.pop_empty to ensure FIFO is not empty
          $display($sformatf({"Time: %0t, INFO: test_PopDataOperationTransaction1 -  ",
                              "FIFO is not empty"}, $time));

          @(cb_pop_clk);
          if (cb_pop_clk.pop_valid == 1) begin
            // Step 3: If cb_pop_clk.pop_empty is deasserted, assert cb_pop_clk.pop_valid
            $display($sformatf({"Time: %0t, INFO: test_PopDataOperationTransaction1 - ",
                                "pop_valid asserted, valid", "data available"}, $time));

            @(cb_pop_clk);
            if (cb_pop_clk.pop_data == expected_pop_data) begin
              // Step 4: Provide data on cb_pop_clk.pop_data
              $display($sformatf({"Time: %0t, INFO: test_PopDataOperationTransaction1 - ",
                                  "Correct data popped: 0x%h"}, $time, pop_data));
            end else begin
              $display($sformatf({"Time: %0t, ERROR: test_PopDataOperationTransaction1 -  ",
                                  "Incorrect data popped.", "Expected: 0x%h, Got: 0x%h"}, $time,
                                   expected_pop_data, pop_data));
              test_failed = 1;
            end

            @(cb_pop_clk);
            if (cb_pop_clk.pop_items == expected_pop_items) begin
              // Step 5: Update cb_pop_clk.pop_items
              $display($sformatf({"Time: %0t, INFO: test_PopDataOperationTransaction1 -  ",
                                  "pop_items correct: %0d"}, $time, pop_items));
            end else begin
              $display($sformatf({"Time: %0t, ERROR: test_PopDataOperationTransaction1 -  ",
                                  "Incorrect pop_items.", "Expected: %0d, Got: %0d"}, $time,
                                   expected_pop_items, pop_items));
              test_failed = 1;
            end

          end else begin
            $display($sformatf({"Time: %0t, ERROR: test_PopDataOperationTransaction1 - ",
                                "pop_valid not asserted ", "when expected"}, $time));
            test_failed = 1;
          end
        end else begin
          $display($sformatf({"Time: %0t, ERROR: test_PopDataOperationTransaction1 - ",
                              "FIFO is empty when it ", "should not be"}, $time));
          test_failed = 1;
        end

        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_PopDataOperationTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_PopDataOperationTransaction1", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditInitializationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_CreditInitializationTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Test the initialization of the credit system for FIFO push control.
        // Local variables declaration
        int test_failed = -1;
        localparam int CreditWidth = $clog2(MaxCredit + 1);
        logic [CreditWidth-1:0] expected_credit_count_push;
        logic [CreditWidth-1:0] initial_credit_value;

        // Initialize the credit system
        initial_credit_value =
            $urandom_range(1, MaxCredit);  // Random initial credit value within valid range
        @(cb_push_clk);
        cb_push_clk.credit_initial_push <= initial_credit_value;
        $display($sformatf({"Time: %0t, INFO: test_CreditInitializationTransaction1 - Driving ",
                            "credit_initial_push=0x%h"}, $time, initial_credit_value));

        // Wait for the credit system to initialize
        @(cb_push_clk);
        expected_credit_count_push = initial_credit_value;
        @(cb_push_clk);
        @(cb_push_clk);
        @(cb_push_clk);
        @(cb_push_clk);
        @(cb_push_clk);
        @(cb_push_clk);
        @(cb_push_clk);

        // Check if the credit_count_push is initialized correctly
        if (cb_push_clk.credit_count_push !== expected_credit_count_push) begin
          $display($sformatf({"Time: %0t, ERROR: test_CreditInitializationTransaction1 - ",
                              "Check failed. ", "Expected credit_count_push=0x%h, got 0x%h"},
                               $time, expected_credit_count_push, cb_push_clk.credit_count_push));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_CreditInitializationTransaction1 - ", "Check passed. ",
                   "Expected value for credit_count_push is the same as the observed value (both ",
                   "are 0x%h)."}, $time, credit_count_push));
          if (test_failed != 1) test_failed = 0;
        end

        // Report the test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_CreditInitializationTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_CreditInitializationTransaction1", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditWithholdingTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_CreditWithholdingTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Test the credit withholding functionality by setting `credit_withhold_push` and verifying the reduction in `credit_count_push` and update of `credit_available_push`.

        // Local variables declaration
        int test_failed = -1;
        localparam int CreditWidth = $clog2(MaxCredit + 1);
        logic [CreditWidth-1:0] initial_credit;
        logic [CreditWidth-1:0] withhold_credit;
        logic [CreditWidth-1:0] expected_credit_count;
        logic [CreditWidth-1:0] expected_credit_available;

        // Preconditions: Initialize credits
        initial_credit  = $urandom_range(1, MaxCredit);
        withhold_credit = $urandom_range(0, initial_credit);

        // Apply initial credit
        @(cb_push_clk);
        cb_push_clk.credit_initial_push <= initial_credit;
        $display($sformatf({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - ",
                            "Initial credit set to %0d"}, $time, initial_credit));

        // Wait for credit initialization
        @(cb_push_clk);

        // Apply credit withholding
        @(cb_push_clk);
        cb_push_clk.credit_withhold_push <= withhold_credit;
        $display(
            $sformatf(
                {"Time: %0t, INFO: test_CreditWithholdingTransaction1 - Withholding credit set to ",
                 "%0d"}, $time, withhold_credit));

        // Calculate expected values
        expected_credit_count = initial_credit - withhold_credit;
        expected_credit_available = expected_credit_count;

        // Wait for credit update
        @(cb_push_clk);

        // Check credit count
        if (cb_push_clk.credit_count_push !== expected_credit_count) begin
          $display($sformatf({"Time: %0t, ERROR: test_CreditWithholdingTransaction1 - ",
                              "Credit count mismatch. ", "Expected %0d, got %0d"}, $time,
                               expected_credit_count, credit_count_push));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - ",
                              "Credit count check passed. ", "Expected and got %0d"}, $time,
                               expected_credit_count));
          if (test_failed != 1) test_failed = 0;
        end

        // Check available credit
        if (cb_push_clk.credit_available_push !== expected_credit_available) begin
          $display($sformatf({"Time: %0t, ERROR: test_CreditWithholdingTransaction1 - ",
                              "Available credit ", "mismatch. ", "Expected %0d, got %0d"}, $time,
                               expected_credit_available, credit_available_push));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - ",
                              "Available credit check ", "passed. ", "Expected and got %0d"},
                               $time, expected_credit_available));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_CreditWithholdingTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_CreditWithholdingTransaction1", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditAvailabilityMonitoringTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: ",
                            "test_CreditAvailabilityMonitoringTransaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Monitor available credits and update `credit_available_push` to reflect current credit availability.

        // Local variables declaration
        int test_failed = -1;
        logic [CreditWidth-1:0] expected_credit_available_push;
        logic [CreditWidth-1:0] random_credit_initial_push;
        logic [CreditWidth-1:0] random_credit_withhold_push;

        // Initialize the test environment
        random_credit_initial_push  = $urandom_range(0, MaxCredit);
        random_credit_withhold_push = $urandom_range(0, MaxCredit);

        // Apply initial credit and withhold values
        @(cb_push_clk);
        cb_push_clk.credit_initial_push  <= random_credit_initial_push;
        cb_push_clk.credit_withhold_push <= random_credit_withhold_push;

        // Calculate expected credit availability
        expected_credit_available_push = random_credit_initial_push - random_credit_withhold_push;
        if (expected_credit_available_push < 0) begin
          expected_credit_available_push = 0;
        end

        // Wait for the credit count to stabilize
        @(cb_push_clk);

        // Check if the credit_available_push matches the expected value
        if (cb_push_clk.credit_available_push !== expected_credit_available_push) begin
          $display($sformatf({"Time: %0t, ERROR: test_CreditAvailabilityMonitoringTransaction1 -",
                              " Check failed. ", "Expected credit_available_push = 0x%h, got 0x%h"
                               }, $time, expected_credit_available_push, credit_available_push));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_CreditAvailabilityMonitoringTransaction1 - ",
                   "Check passed. ",
                   "Expected value for credit_available_push is the same as the observed value ",
                   "(both are 0x%h)."}, $time, credit_available_push));
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_CreditAvailabilityMonitoringTransaction1", $time);
        end else begin
          $display("Time: %0t, FAILED: test_CreditAvailabilityMonitoringTransaction1", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

  asrt_push_credit_stall_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(
      push_credit_stall
  )))
  else $error("push_credit_stall is X after reset!");

  asrt_push_valid_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(push_valid)))
  else $error("push_valid is X after reset!");

  asrt_push_data_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(push_data)))
  else $error("push_data is X after reset!");

  asrt_credit_initial_push_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(
      credit_initial_push
  )))
  else $error("credit_initial_push is X after reset!");

  asrt_pop_ready_not_unknown :
  assert property (@(posedge pop_clk) disable iff (pop_rst !== 1'b0) (!$isunknown(pop_ready)))
  else $error("pop_ready is X after reset!");

  asrt_credit_withhold_push_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(
      credit_withhold_push
  )))
  else $error("credit_withhold_push is X after reset!");

endmodule
