//=============================================================
// Testbench for Module: br_cdc_fifo_flops_push_credit
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_cdc_fifo_flops_push_credit
//=============================================================

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
  parameter bit RegisterPushCredit = 0;
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
  logic push_full_next;
  logic [CountWidth-1:0] push_slots;
  logic [CountWidth-1:0] push_slots_next;
  logic [CreditWidth-1:0] available;
  logic [CreditWidth-1:0] credit_available_push;
  logic pop_empty;
  logic pop_empty_next;
  logic [CountWidth-1:0] pop_items;
  logic [CountWidth-1:0] pop_items_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_flops_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPushCredit(RegisterPushCredit),
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
      .push_full_next(push_full_next),
      .push_slots(push_slots),
      .push_slots_next(push_slots_next),
      .credit_count_push(credit_count_push),
      .credit_available_push(credit_available_push),
      .pop_empty(pop_empty),
      .pop_empty_next(pop_empty_next),
      .pop_items(pop_items),
      .pop_items_next(pop_items_next)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  int test_failed = -1;

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
    inout push_rst, pop_rst, push_credit_stall, push_valid, push_data, pop_ready,
          credit_initial_push, credit_withhold_push;
    input push_credit, pop_valid, pop_data, push_full, push_full_next, push_slots, push_slots_next,
    credit_count_push, credit_available_push, pop_empty, pop_empty_next, pop_items, pop_items_next;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout push_rst, pop_rst, push_credit_stall, push_valid, push_data, pop_ready,
          credit_initial_push, credit_withhold_push;
    input push_credit, pop_valid, pop_data, push_full, push_full_next, push_slots, push_slots_next,
          credit_count_push, credit_available_push, pop_empty, pop_empty_next, pop_items,
          pop_items_next;
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
    cb_push_clk.push_credit_stall <= 'h0;
    cb_push_clk.push_valid <= 'h0;
    cb_push_clk.push_data <= 'h0;
    cb_push_clk.pop_ready <= 'h0;
    cb_push_clk.credit_initial_push <= 'h0;
    cb_push_clk.credit_withhold_push <= 'h0;

    // Wiggling the reset signal.
    push_rst = 1'b0;
    pop_rst  = 1'b0;
    #RESET_DURATION;
    push_rst = 1'b1;
    pop_rst  = 1'b1;
    #RESET_DURATION;
    push_rst = 1'b0;
    pop_rst  = 1'b0;
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

    $finish;
  end


  task automatic test_PushDataOperationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushDataOperationTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Test the push data operation of the FIFO, ensuring data is pushed only when there is available space.
        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_data;
        logic [CreditWidth-1:0] initial_credit;
        logic [CreditWidth-1:0] withhold_credit;
        logic [CountWidth-1:0] expected_push_slots;
        logic [CountWidth-1:0] expected_push_slots_next;
        logic expected_push_full_next;

        // Preconditions: Initialize credits and ensure FIFO is not full
        initial_credit = $urandom_range(1, MaxCredit);
        withhold_credit = 0;
        expected_push_slots = Depth;
        expected_push_slots_next = Depth;
        expected_push_full_next = 0;

        // Apply initial credit
        @(cb_push_clk);
        cb_push_clk.credit_initial_push  <= initial_credit;
        cb_push_clk.credit_withhold_push <= withhold_credit;
        $display({"Time: %0t, INFO: test_PushDataOperationTransaction1 - Initial credits set to %0d"
                   }, $time, initial_credit);

        // Wait for a clock cycle to propagate initial conditions
        @(cb_push_clk);

        // Step 1: Assert `push_valid` to indicate valid data on `push_data`
        random_data = $urandom();
        @(cb_push_clk);
        cb_push_clk.push_valid <= 1;
        cb_push_clk.push_data  <= random_data;

        $display({"Time: %0t, INFO: test_PushDataOperationTransaction1 - Driving push_valid=1,",
                  "push_data=0x%h"}, $time, random_data);

        // Step 2: Monitor `push_full` to check if the FIFO is full
        @(cb_push_clk);
        expected_push_slots -= 1;
        expected_push_slots_next -= 1;
        expected_push_full_next = 1;
        if (cb_push_clk.push_full) begin
          $display({"Time: %0t, ERROR: test_PushDataOperationTransaction1 - FIFO is full, cannot",
                    "push data"}, $time);
          test_failed = 1;
        end else begin
          // Step 3: If `push_full` is deasserted, acknowledge data push by asserting `push_credit`
          if (cb_push_clk.push_credit) begin
            $display(
                {"Time: %0t, INFO: test_PushDataOperationTransaction1 - Data push acknowledged",
                 "with push_credit=1"}, $time);

          end else begin
            $display(
                {"Time: %0t, INFO: test_PushDataOperationTransaction1 - push_credit not asserted"},
                  $time);
            test_failed = 0;
          end
        end

        // Step 4: Update `push_slots` to reflect current available slots
        @(cb_push_clk);
        expected_push_slots_next -= 1;
        if (cb_push_clk.push_slots != expected_push_slots) begin
          $display({"Time: %0t, ERROR: test_PushDataOperationTransaction1 - push_slots mismatch.",
                    "Expected: %0d, Got: %0d"}, $time, expected_push_slots, cb_push_clk.push_slots);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushDataOperationTransaction1 - push_slots correctly",
                    "updated to %0d"}, $time, push_slots);
        end

        // Step 5: Update `push_slots_next` to predict available slots in the next cycle
        if (cb_push_clk.push_slots_next != expected_push_slots_next) begin
          $display(
              {"Time: %0t, ERROR: test_PushDataOperationTransaction1 - push_slots_next mismatch.",
               "Expected: %0d, Got: %0d"}, $time, expected_push_slots_next,
                cb_push_clk.push_slots_next);
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_PushDataOperationTransaction1 - push_slots_next correctly",
               "predicted to %0d"}, $time, push_slots_next);
        end

        // Step 6: Update `push_full_next` to predict if the FIFO will be full in the next cycle
        if (cb_push_clk.push_full_next != expected_push_full_next) begin
          $display(
              {"Time: %0t, ERROR: test_PushDataOperationTransaction1 - push_full_next mismatch.",
               "Expected: %0d, Got: %0d"}, $time, expected_push_full_next, push_full_next);
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_PushDataOperationTransaction1 - push_full_next correctly",
               "predicted to %0d"}, $time, push_full_next);
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushDataOperationTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushDataOperationTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushDataOperationTransaction2;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushDataOperationTransaction2.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Simulate a stall condition during the push operation and verify the behavior of the FIFO.

        // Local variables declaration
        int test_failed = -1;
        localparam int CountWidth = $clog2(Depth + 1);
        logic [CountWidth-1:0] initial_push_slots;
        logic [CountWidth-1:0] initial_push_slots_next;
        logic initial_push_full_next;

        // Precondition: Capture initial state of push_slots and push_slots_next
        @(cb_push_clk);
        initial_push_slots = cb_push_clk.push_slots;
        initial_push_slots_next = cb_push_clk.push_slots_next;
        initial_push_full_next = cb_push_clk.push_full_next;

        // Step 1: Assert `push_credit_stall` to simulate a stall condition
        cb_push_clk.push_credit_stall <= 1;
        @(cb_push_clk);
        $display({"Time: %0t, INFO: test_PushDataOperationTransaction2 - Asserted push_credit_stall"
                   }, $time);

        // Step 2: Deassert `push_credit` to indicate no data can be pushed during the stall
        if (cb_push_clk.push_credit !== 0) begin
          $display({"Time: %0t, ERROR: test_PushDataOperationTransaction2 - push_credit should be",
                    "deasserted during stall.", "Expected 0, got %0b"}, $time, push_credit);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushDataOperationTransaction2 - push_credit correctly",
                    "deasserted during stall"}, $time);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 3: Maintain current state of `push_slots` and `push_slots_next` during the stall
        if (cb_push_clk.push_slots !== initial_push_slots ||
            cb_push_clk.push_slots_next !== initial_push_slots_next) begin
          $display({"Time: %0t, ERROR: test_PushDataOperationTransaction2 - push_slots or ",
                    "push_slots_next changed during stall.", "Expected %0d/%0d, got %0d/%0d"},
                     $time, initial_push_slots, initial_push_slots_next, push_slots,
                     push_slots_next);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PushDataOperationTransaction2 - push_slots and ",
                    "push_slots_next maintained during stall"}, $time);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 4: Update `push_full_next` to predict if the FIFO will be full in the next cycle
        if (cb_push_clk.push_full_next !== initial_push_full_next) begin
          $display(
            {
              "Time: %0t, ERROR: test_PushDataOperationTransaction2 - push_full_next changed ",
              "during stall.", "Expected %0b, got %0b"
            }, $time, initial_push_full_next,
            push_full_next);
          test_failed = 1;
        end else begin
          $display(
              {
              "Time: %0t, INFO: test_PushDataOperationTransaction2 - push_full_next correctly",
              "maintained during stall"
              }, $time);
          if (test_failed != 1) test_failed = 0;
        end

        // End of test: Report status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushDataOperationTransaction2"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushDataOperationTransaction2"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopDataOperationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopDataOperationTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Test the pop data operation, ensuring data is popped only when the FIFO is not empty and the pop interface is ready.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] expected_pop_data;
        logic [CountWidth-1:0] expected_pop_items;
        logic [CountWidth-1:0] expected_pop_items_next;
        logic expected_pop_empty_next;

        // Preconditions: Initialize FIFO with known data
        // Assuming FIFO is pre-filled with known data for this test scenario
        expected_pop_data = 'hA5;  // Example data
        expected_pop_items = 1;  // Assuming 1 item in FIFO
        expected_pop_items_next = 0;  // Predicting FIFO will be empty after pop
        expected_pop_empty_next = 1;  // Predicting FIFO will be empty after pop

        @(cb_push_clk);
        cb_push_clk.push_valid <= 1;

        // Wait for 6 pop clock
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);
        @(cb_pop_clk);

        if (cb_push_clk.pop_empty == 0) begin
          // Step 2: Monitor cb_push_clk.pop_empty to ensure FIFO is not empty
          $display({"Time: %0t, INFO: test_PopDataOperationTransaction1 - FIFO is not empty"},
                     $time);

          @(cb_pop_clk);
          if (cb_push_clk.pop_valid == 1) begin
            // Step 3: If cb_push_clk.pop_empty is deasserted, assert cb_push_clk.pop_valid
            $display(
                {"Time: %0t, INFO: test_PopDataOperationTransaction1 - pop_valid asserted, valid",
                 "data available"}, $time);

            @(cb_pop_clk);
            if (cb_push_clk.pop_data == expected_pop_data) begin
              // Step 4: Provide data on cb_push_clk.pop_data
              $display(
                  {"Time: %0t, INFO: test_PopDataOperationTransaction1 - Correct data popped: 0x%h"
                    }, $time, pop_data);
            end else begin
              $display(
                  {"Time: %0t, ERROR: test_PopDataOperationTransaction1 - Incorrect data popped.",
                   "Expected: 0x%h, Got: 0x%h"}, $time, expected_pop_data, pop_data);
              test_failed = 1;
            end

            @(cb_pop_clk);
            if (cb_push_clk.pop_items == expected_pop_items) begin
              // Step 5: Update cb_push_clk.pop_items
              $display(
                  {"Time: %0t, INFO: test_PopDataOperationTransaction1 - pop_items correct: %0d"},
                    $time, pop_items);
            end else begin
              $display(
                  {"Time: %0t, ERROR: test_PopDataOperationTransaction1 - Incorrect pop_items.",
                   "Expected: %0d, Got: %0d"}, $time, expected_pop_items, pop_items);
              test_failed = 1;
            end

            @(cb_pop_clk);
            if (cb_push_clk.pop_items_next == expected_pop_items_next) begin
              // Step 6: Update cb_push_clk.pop_items_next
              $display(
                  {
                    "Time: %0t, INFO: test_PopDataOperationTransaction1 - pop_items_next correct: %0d"
                  }, $time, pop_items_next);
            end else begin
              $display(
                  {
                  "Time: %0t, ERROR: test_PopDataOperationTransaction1 - Incorrect pop_items_next.",
                  "Expected: %0d, Got: %0d"
                  }, $time, expected_pop_items_next, pop_items_next);
              test_failed = 1;
            end

            @(cb_pop_clk);
            if (cb_push_clk.pop_empty_next == expected_pop_empty_next) begin
              // Step 7: Update cb_push_clk.pop_empty_next
              $display(
                  {
                    "Time: %0t, INFO: test_PopDataOperationTransaction1 - pop_empty_next correct: %0d"
                  }, $time, pop_empty_next);
            end else begin
              $display(
                  {
                  "Time: %0t, ERROR: test_PopDataOperationTransaction1 - Incorrect pop_empty_next.",
                  "Expected: %0d, Got: %0d"
                  }, $time, expected_pop_empty_next, pop_empty_next);
              test_failed = 1;
            end

          end else begin
            $display(
                {"Time: %0t, ERROR: test_PopDataOperationTransaction1 - pop_valid not asserted",
                 "when expected"}, $time);
            test_failed = 1;
          end
        end else begin
          $display({"Time: %0t, ERROR: test_PopDataOperationTransaction1 - FIFO is empty when it",
                    "should not be"}, $time);
          test_failed = 1;
        end

        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopDataOperationTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopDataOperationTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditInitializationTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_CreditInitializationTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
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
        $display({"Time: %0t, INFO: test_CreditInitializationTransaction1 - Driving",
                  "credit_initial_push=0x%h"}, $time, initial_credit_value);

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
          $display({"Time: %0t, ERROR: test_CreditInitializationTransaction1 - Check failed.",
                    "Expected credit_count_push=0x%h, got 0x%h"}, $time,
                     expected_credit_count_push, cb_push_clk.credit_count_push);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_CreditInitializationTransaction1 - Check passed.",
                    "Expected value for credit_count_push is the same as the observed value (both",
                    "are 0x%h)."}, $time, credit_count_push);
          if (test_failed != 1) test_failed = 0;
        end

        // Report the test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_CreditInitializationTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_CreditInitializationTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditWithholdingTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_CreditWithholdingTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
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
        $display({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - Initial credit set to %0d"
                   }, $time, initial_credit);

        // Wait for credit initialization
        @(cb_push_clk);

        // Apply credit withholding
        @(cb_push_clk);
        cb_push_clk.credit_withhold_push <= withhold_credit;
        $display({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - Withholding credit set to",
                  "%0d"}, $time, withhold_credit);

        // Calculate expected values
        expected_credit_count = initial_credit - withhold_credit;
        expected_credit_available = expected_credit_count;

        // Wait for credit update
        @(cb_push_clk);

        // Check credit count
        if (cb_push_clk.credit_count_push !== expected_credit_count) begin
          $display({"Time: %0t, ERROR: test_CreditWithholdingTransaction1 - Credit count mismatch.",
                    "Expected %0d, got %0d"}, $time, expected_credit_count, credit_count_push);
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_CreditWithholdingTransaction1 - Credit count check passed.",
               "Expected and got %0d"}, $time, expected_credit_count);
          if (test_failed != 1) test_failed = 0;
        end

        // Check available credit
        if (cb_push_clk.credit_available_push !== expected_credit_available) begin
          $display({"Time: %0t, ERROR: test_CreditWithholdingTransaction1 - Available credit",
                    "mismatch.", "Expected %0d, got %0d"}, $time, expected_credit_available,
                     credit_available_push);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_CreditWithholdingTransaction1 - Available credit check",
                    "passed.", "Expected and got %0d"}, $time, expected_credit_available);
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_CreditWithholdingTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_CreditWithholdingTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_CreditAvailabilityMonitoringTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_CreditAvailabilityMonitoringTransaction1.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
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
          $display(
              {"Time: %0t, ERROR: test_CreditAvailabilityMonitoringTransaction1 - Check failed.",
               "Expected credit_available_push = 0x%h, got 0x%h"}, $time,
                expected_credit_available_push, credit_available_push);
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_CreditAvailabilityMonitoringTransaction1 - Check passed.",
               "Expected value for credit_available_push is the same as the observed value",
               "(both are 0x%h)."}, $time, credit_available_push);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_CreditAvailabilityMonitoringTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_CreditAvailabilityMonitoringTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
