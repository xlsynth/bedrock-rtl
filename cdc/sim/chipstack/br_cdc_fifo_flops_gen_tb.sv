//=============================================================
// Testbench for Module: br_cdc_fifo_flops
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_cdc_fifo_flops
//=============================================================

module tb;
  timeunit 1ns; timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  parameter CLOCK_FREQ = 100;  // Clock frequency in MHz
  parameter RESET_DURATION = 100;  // Reset duration in ns
  parameter TIMEOUT = 10000000;  // Timeout value in ns
  parameter PER_TASK_TIMEOUT = 1000000;  // Timeout value for each task in ns
  parameter DRAIN_TIME = 10000;  // Time to observe all results in ns
  parameter CLOCK_FREQ_NS_CONVERSION_FACTOR = 1000;  // Conversion factor to nanoseconds
  parameter NO_ASSERTS_ON_RESET = 0;  // Disable assertions during reset
  parameter DISABLE_CHECKS = 0;  // Disable checks


  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int Depth = 2;
  parameter int Width = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int NumSyncStages = 3;
  parameter int FlopRamDepthTiles = 1;
  parameter int FlopRamWidthTiles = 1;
  parameter int FlopRamAddressDepthStages = 0;
  parameter int FlopRamReadDataDepthStages = 0;
  parameter int FlopRamReadDataWidthStages = 0;
  parameter bit EnableCoverPushBackpressure = 1;
  parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure;
  parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2((Depth + 1));

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
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic push_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic push_full;
  logic push_full_next;
  logic [CountWidth-1:0] push_slots;
  logic [CountWidth-1:0] push_slots_next;
  logic pop_empty;
  logic pop_empty_next;
  logic [CountWidth-1:0] pop_items;
  logic [CountWidth-1:0] pop_items_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumSyncStages(NumSyncStages),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) dut (
      .push_clk(push_clk),
      .pop_clk(pop_clk),
      .push_rst(push_rst),
      .pop_rst(pop_rst),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .push_ready(push_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .push_full(push_full),
      .push_full_next(push_full_next),
      .push_slots(push_slots),
      .push_slots_next(push_slots_next),
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
    inout push_rst, pop_rst, push_valid, push_data, pop_ready;
    input push_ready, pop_valid, pop_data, push_full, push_full_next, push_slots, push_slots_next, pop_empty, pop_empty_next, pop_items, pop_items_next;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout push_rst, pop_rst, push_valid, push_data, pop_ready;
    input push_ready, pop_valid, pop_data, push_full, push_full_next, push_slots, push_slots_next, pop_empty, pop_empty_next, pop_items, pop_items_next;
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
    cb_push_clk.push_valid <= 'h0;
    cb_push_clk.push_data  <= 'h0;
    cb_push_clk.pop_ready  <= 'h0;

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
    test_PushDataFlowControl();

    reset_dut();
    test_PushStatusMonitoring();

    reset_dut();
    test_PopDataFlowControl();

    reset_dut();
    test_PopStatusPrediction();

    $finish;
  end


  task automatic test_PushDataFlowControl;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushDataFlowControl.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Manage the flow of data being pushed into the FIFO, ensuring data is only pushed when there is available space and the push is valid.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_data;
        logic [CountWidth-1:0] expected_push_slots;
        logic [CountWidth-1:0] expected_push_slots_next;
        logic expected_push_full_next;

        // Initial setup
        expected_push_slots = Depth;
        expected_push_slots_next = Depth;
        expected_push_full_next = 0;

        // Wait for a clock cycle to ensure proper stimulus propagation
        @(cb_push_clk);

        // Step 1: Assert `push_valid` to indicate that valid data is available for pushing.
        cb_push_clk.push_valid <= 1;
        random_data = $urandom();
        cb_push_clk.push_data <= random_data;
        $display({"Time: %0t, INFO: test_PushDataFlowControl - Driving push_valid=1, push_data=0x%h"
                   }, $time, random_data);

        // Step 2: Monitor `push_full` to determine if the FIFO is full.
        @(cb_push_clk);
        if (cb_push_clk.push_full) begin
          $display({"Time: %0t, INFO: test_PushDataFlowControl - FIFO is full, push_full=1"},
                     $time);
          cb_push_clk.push_valid <= 0;  // Stop pushing data if FIFO is full
        end else begin
          // Step 3: If `push_full` is not asserted, expect `push_ready` to be asserted.
          if (cb_push_clk.push_ready) begin
            $display({"Time: %0t, INFO: test_PushDataFlowControl - FIFO is ready, push_ready=1"},
                       $time);

            // Step 4: If `push_ready` is asserted, the data is accepted.
            expected_push_slots = expected_push_slots - 1;
            expected_push_slots_next = expected_push_slots_next - 1;
            expected_push_full_next = (expected_push_slots_next == 0);

            // Step 5: Update `push_slots` and `push_slots_next` to reflect the new state.
            if (cb_push_clk.push_slots != expected_push_slots) begin
              $display({"Time: %0t, ERROR: test_PushDataFlowControl - push_slots mismatch.",
                        "Expected %0d, got %0d"}, $time, expected_push_slots, push_slots);
              test_failed = 1;
            end else begin
              $display({"Time: %0t, INFO: test_PushDataFlowControl - push_slots check passed.",
                        "Expected %0d, got %0d"}, $time, expected_push_slots, push_slots);
            end

            if (cb_push_clk.push_slots_next != expected_push_slots_next) begin
              $display({"Time: %0t, ERROR: test_PushDataFlowControl - push_slots_next mismatch.",
                        "Expected %0d, got %0d"}, $time, expected_push_slots_next, push_slots_next);
              test_failed = 1;
            end else begin
              $display({"Time: %0t, INFO: test_PushDataFlowControl - push_slots_next check passed.",
                        "Expected %0d, got %0d"}, $time, expected_push_slots_next, push_slots_next);
            end

            // Step 6: Update `push_full_next` to predict if the FIFO will be full after the current transaction.
            if (cb_push_clk.push_full_next != expected_push_full_next) begin
              $display({"Time: %0t, ERROR: test_PushDataFlowControl - push_full_next mismatch.",
                        "Expected %0d, got %0d"}, $time, expected_push_full_next, push_full_next);
              test_failed = 1;
            end else begin
              $display({"Time: %0t, INFO: test_PushDataFlowControl - push_full_next check passed.",
                        "Expected %0d, got %0d"}, $time, expected_push_full_next, push_full_next);
            end

          end else begin
            $display({"Time: %0t, ERROR: test_PushDataFlowControl - push_ready not asserted when",
                      "expected"}, $time);
            test_failed = 1;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushDataFlowControl"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushDataFlowControl"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushStatusMonitoring;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushStatusMonitoring.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Monitor and update the status of the FIFO to determine if it is full or has available slots, affecting the ability to push more data.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_push_data;
        logic [CountWidth-1:0] expected_push_slots;
        logic [CountWidth-1:0] expected_push_slots_next;
        logic expected_push_full;

        // Initial setup
        @(cb_push_clk);
        cb_push_clk.push_valid <= 0;
        cb_push_clk.push_data  <= 0;
        expected_push_slots = Depth;
        expected_push_slots_next = Depth;
        expected_push_full = 0;

        // Begin test scenario
        repeat (Depth + 2) begin
          @(cb_push_clk);
          random_push_data = $urandom();
          cb_push_clk.push_valid <= 1;
          cb_push_clk.push_data  <= random_push_data;
          $display({"Time: %0t, INFO: test_PushStatusMonitoring - Driving push_valid=1,",
                    "push_data=0x%h"}, $time, random_push_data);

          @(cb_push_clk);
          if (cb_push_clk.push_ready) begin
            expected_push_slots = expected_push_slots - 1;
            expected_push_slots_next = expected_push_slots_next - 1;
          end

          if (expected_push_slots == 0) begin
            expected_push_full = 1;
          end else begin
            expected_push_full = 0;
          end

          // Check push_slots
          if (cb_push_clk.push_slots !== expected_push_slots) begin
            $display({"Time: %0t, ERROR: test_PushStatusMonitoring - Check failed.",
                      "Expected push_slots=%0d, got %0d"}, $time, expected_push_slots, push_slots);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PushStatusMonitoring - Check passed.",
                      "Expected push_slots=%0d, got %0d"}, $time, expected_push_slots, push_slots);
            if (test_failed != 1) test_failed = 0;
          end

          // Check push_slots_next
          if (cb_push_clk.push_slots_next !== expected_push_slots_next) begin
            $display({"Time: %0t, ERROR: test_PushStatusMonitoring - Check failed.",
                      "Expected push_slots_next=%0d, got %0d"}, $time, expected_push_slots_next,
                       push_slots_next);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PushStatusMonitoring - Check passed.",
                      "Expected push_slots_next=%0d, got %0d"}, $time, expected_push_slots_next,
                       push_slots_next);
            if (test_failed != 1) test_failed = 0;
          end

          // Check push_full
          if (cb_push_clk.push_full !== expected_push_full) begin
            $display({"Time: %0t, ERROR: test_PushStatusMonitoring - Check failed.",
                      "Expected push_full=%0b, got %0b"}, $time, expected_push_full, push_full);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PushStatusMonitoring - Check passed.",
                      "Expected push_full=%0b, got %0b"}, $time, expected_push_full, push_full);
            if (test_failed != 1) test_failed = 0;
          end

          // Check push_ready
          if (cb_push_clk.push_full && cb_push_clk.push_ready) begin
            $display({"Time: %0t, ERROR: test_PushStatusMonitoring - Check failed.",
                      "push_ready should be deasserted when push_full is asserted"}, $time);
            test_failed = 1;
          end else if (!cb_push_clk.push_full && !cb_push_clk.push_ready) begin
            $display({"Time: %0t, ERROR: test_PushStatusMonitoring - Check failed.",
                      "push_ready should be asserted when push_full is deasserted"}, $time);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PushStatusMonitoring - Check passed for push_ready"},
                       $time);
            if (test_failed != 1) test_failed = 0;
          end

          // Disable further stimulus application
          cb_push_clk.push_valid <= 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushStatusMonitoring"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushStatusMonitoring"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopDataFlowControl;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopDataFlowControl.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Manage the flow of data being popped from the FIFO, ensuring data is only popped when the FIFO is not empty and the pop interface is ready to accept data.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] expected_pop_data;
        logic [CountWidth-1:0] expected_pop_items;
        logic pop_ready_flag;

        // Initial setup
        pop_ready_flag = 1;
        expected_pop_items = 0;

        // Ensure adequate stimulus propagation time
        @(cb_pop_clk);

        // Step 1: Set `pop_ready` to indicate readiness to receive data
        cb_pop_clk.pop_ready <= pop_ready_flag;
        $display({"Time: %0t, INFO: test_PopDataFlowControl - Set pop_ready to %0d"}, $time,
                   pop_ready_flag);

        // Step 2: Monitor `pop_empty` to ensure the FIFO is not empty
        if (!cb_push_clk.pop_empty) begin
          // Step 3: If `pop_empty` is false, expect `pop_valid` to be asserted
          if (cb_push_clk.pop_valid) begin
            // Step 4: Provide data on `pop_data`
            expected_pop_data = cb_push_clk.pop_data;
            $display({"Time: %0t, INFO: test_PopDataFlowControl - pop_valid asserted, pop_data=0x%h"
                       }, $time, pop_data);

            // Step 5: Update `pop_items` to reflect the number of items remaining in the FIFO
            expected_pop_items = cb_push_clk.pop_items - 1;
            $display({"Time: %0t, INFO: test_PopDataFlowControl - Expected pop_items after pop: %0d"
                       }, $time, expected_pop_items);

            // Perform checks
            if (cb_push_clk.pop_items_next != expected_pop_items) begin
              $display({"Time: %0t, ERROR: test_PopDataFlowControl - pop_items_next check failed.",
                        "Expected %0d, got %0d"}, $time, expected_pop_items, pop_items_next);
              test_failed = 1;
            end else begin
              $display({"Time: %0t, INFO: test_PopDataFlowControl - pop_items_next check passed.",
                        "Expected and got %0d"}, $time, expected_pop_items);
              if (test_failed != 1) test_failed = 0;
            end
          end else begin
            $display(
                {"Time: %0t, ERROR: test_PopDataFlowControl - pop_valid not asserted when expected"
                  }, $time);
            test_failed = 1;
          end
        end else begin
          $display({"Time: %0t, INFO: test_PopDataFlowControl - FIFO is empty, no pop operation",
                    "performed"}, $time);
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopDataFlowControl"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopDataFlowControl"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopStatusPrediction;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopStatusPrediction.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Predict the status of the FIFO after the next pop operation, calculating the next empty status and the number of items that will remain in the FIFO.

        // Local variables declaration
        int test_failed = -1;
        logic [CountWidth-1:0] expected_pop_items_next;
        logic expected_pop_empty_next;

        // Initial setup
        @(cb_pop_clk);
        cb_pop_clk.pop_ready <= 1'b1;  // Set pop_ready to indicate readiness to pop data
        $display({"Time: %0t, INFO: test_PopStatusPrediction - pop_ready set to 1"}, $time);

        // Calculate expected values
        expected_pop_items_next = cb_push_clk.pop_items - (cb_push_clk.pop_ready && !cb_push_clk.pop_empty);
        expected_pop_empty_next = (expected_pop_items_next == 0);

        // Wait for a clock cycle to allow the DUT to update its outputs
        @(cb_pop_clk);

        // Check pop_items_next
        if (cb_push_clk.pop_items_next !== expected_pop_items_next) begin
          $display({"Time: %0t, ERROR: test_PopStatusPrediction - pop_items_next check failed.",
                    "Expected: %0d, Got: %0d"}, $time, expected_pop_items_next, pop_items_next);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PopStatusPrediction - pop_items_next check passed.",
                    "Expected and got: %0d"}, $time, expected_pop_items_next);
          if (test_failed != 1) test_failed = 0;
        end

        // Check pop_empty_next
        if (cb_push_clk.pop_empty_next !== expected_pop_empty_next) begin
          $display({"Time: %0t, ERROR: test_PopStatusPrediction - pop_empty_next check failed.",
                    "Expected: %b, Got: %b"}, $time, expected_pop_empty_next, pop_empty_next);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_PopStatusPrediction - pop_empty_next check passed.",
                    "Expected and got: %b"}, $time, expected_pop_empty_next);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopStatusPrediction"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopStatusPrediction"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
