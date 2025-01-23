//=============================================================
// Testbench for Module: br_fifo_flops
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_fifo_flops
//=============================================================

module br_fifo_flops_gen_tb;
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
  parameter bit EnableBypass = 1;
  parameter bit RegisterPopOutputs = 0;
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
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic push_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic full;
  logic full_next;
  logic [CountWidth-1:0] slots;
  logic [CountWidth-1:0] slots_next;
  logic empty;
  logic empty_next;
  logic [CountWidth-1:0] items;
  logic [CountWidth-1:0] items_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) dut (
      .clk(clk),
      .rst(rst),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .push_ready(push_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .full(full),
      .full_next(full_next),
      .slots(slots),
      .slots_next(slots_next),
      .empty(empty),
      .empty_next(empty_next),
      .items(items),
      .items_next(items_next)
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
    inout rst, push_valid, push_data, pop_ready;
    input push_ready, pop_valid, pop_data, full, full_next, slots,
          slots_next, empty, empty_next, items, items_next;
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
    cb_clk.push_valid <= 'h0;
    cb_clk.push_data  <= 'h0;
    cb_clk.pop_ready  <= 'h0;

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
    test_PushDataFlowControlTransaction2();

    reset_dut();
    test_PushValidStabilityTransaction1();

    reset_dut();
    test_PopDataRetrievalTransaction1();

    reset_dut();
    test_ItemCountManagementTransaction1();

    reset_dut();
    test_RegisterPopOutputsControlTransaction1();

    $finish;
  end


  task automatic test_PushDataFlowControlTransaction2;
    fork
      // 1) TIMEOUT PROCESS
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushDataFlowControlTransaction2. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end

      // 2) MAIN TEST LOGIC
      begin : main_test
        // Purpose: Manage the flow of data into the FIFO by controlling the push operation,
        // ensuring data is only pushed when there is available space and handling backpressure
        // when the FIFO is full.

        // Local variables
        int               test_failed = 0;  // Use 0 for pass unless we detect an error
        int               push_count = 0;
        int               total_pushes = 16;  // Example: limit to 16 pushes
        logic [Width-1:0] random_data;
        logic             push_valid_flag;

        // Initial setup
        cb_clk.push_valid <= 0;
        cb_clk.push_data  <= '0;
        cb_clk.pop_ready  <= 0;  // Deassert pop initially (you can toggle as needed)
        push_valid_flag = 0;

        // Wait 1 clock for stable environment
        @(cb_clk);

        // Concurrency to handle push logic
        fork
          // A) Control push_valid_flag based on FIFO fullness
          begin : control_push_valid_flag
            while (push_count < total_pushes) begin
              @(cb_clk);  // wait for next clock
              if (cb_clk.full) begin
                // If FIFO is full, stop pushing and possibly enable popping
                push_valid_flag = 0;
                cb_clk.pop_ready <= 1;  // Let the FIFO drain if your design needs it
                $display({"Time: %0t, INFO: FIFO is full, deasserting push_valid."}, $time);
              end else begin
                // If FIFO has space, push data
                push_valid_flag = 1;
                random_data = $urandom();
                $display({"Time: %0t, INFO: FIFO has space, asserting push_valid with data=0x%h."},
                           $time, random_data);
              end
            end
            // Once we've done our required pushes, deassert push_valid
            push_valid_flag = 0;
          end

          // B) Drive push signals based on push_valid_flag
          begin : drive_push
            while (push_count < total_pushes) begin
              @(cb_clk);
              if (push_valid_flag) begin
                cb_clk.push_valid <= 1;
                cb_clk.push_data  <= random_data;
              end else begin
                cb_clk.push_valid <= 0;
              end
            end
            // After finishing all pushes, clean up signals
            cb_clk.push_valid <= 0;
          end

          // C) Monitor push_ready to count successful pushes
          begin : monitor_push_ready
            while (push_count < total_pushes) begin
              @(cb_clk);
              if (cb_clk.push_ready && push_valid_flag) begin
                push_count++;
                $display({"Time: %0t, INFO: Push successful. ", "push_count=%0d"}, $time,
                           push_count);
              end else if (!cb_clk.push_ready && push_valid_flag) begin
                $display({"Time: %0t, INFO: push_ready deasserted, waiting to push data."}, $time);
              end
            end
          end
        join  // Wait for all three threads to finish

        // Final reporting
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushDataFlowControlTransaction2"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushDataFlowControlTransaction2"}, $time);
        end
      end
    join_any
    disable fork;  // Terminate any remaining processes in the fork
  endtask


  task automatic test_PushValidStabilityTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushValidStabilityTransaction1. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Ensure that the `push_valid` signal remains stable during backpressure conditions, maintaining consistent signaling for data validity.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_push_data;
        logic stable_push_valid;

        // Initial setup
        @(cb_clk);
        cb_clk.rst <= 1;
        @(cb_clk);
        cb_clk.rst <= 0;
        @(cb_clk);

        // Step 1: Assert `push_valid` to indicate a valid push operation
        random_push_data  = $urandom();
        stable_push_valid = 1;
        cb_clk.push_valid <= stable_push_valid;
        cb_clk.push_data  <= random_push_data;
        $display({"Time: %0t, INFO: test_PushValidStabilityTransaction1 - Driving push_valid=1, ",
                  "push_data=0x%h"}, $time, random_push_data);

        // Step 2: Monitor `push_valid` for stability during backpressure
        fork
          begin
            while (!cb_clk.push_ready) begin
              @(cb_clk);
              if (cb_clk.push_valid !== stable_push_valid) begin
                $display(
                    {"Time: %0t, ERROR: test_PushValidStabilityTransaction1 - push_valid is not ",
                     "stable during backpressure. ", "Expected %0b, got %0b"}, $time,
                      stable_push_valid, cb_clk.push_valid);
                test_failed = 1;
              end
            end
          end
        join

        // Step 3: Assert `push_ready` when data can be accepted
        @(cb_clk);
        cb_clk.pop_ready <= 1;
        $display({"Time: %0t, INFO: test_PushValidStabilityTransaction1 - pop_ready asserted"},
                   $time);

        // Step 4: If backpressure occurs, ensure `push_valid` remains stable until `push_ready` is asserted again
        @(cb_clk);
        if (cb_clk.push_ready && cb_clk.push_valid === stable_push_valid) begin
          $display({"Time: %0t, INFO: test_PushValidStabilityTransaction1 - push_valid remained ",
                    "stable during backpressure"}, $time);
          if (test_failed != 1) test_failed = 0;
        end else begin
          $display({"Time: %0t, ERROR: test_PushValidStabilityTransaction1 - push_valid did not ",
                    "remain stable during backpressure"}, $time);
          test_failed = 1;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushValidStabilityTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushValidStabilityTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopDataRetrievalTransaction1;
    fork
      // (1) Timeout thread
      begin : timeout_thread
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopDataRetrievalTransaction1. ",
                  "Stimulus not observed or needs more time to finish."}, $time);
        // If you want the test to end on timeout:
        disable test_thread;
      end

      // (2) Main test thread
      begin : test_thread
        int               test_failed = -1;
        logic [Width-1:0] expected_pop_data;
        logic             pop_ready_flag;
        int               i;

        // Wait one clock cycle for everything to settle
        @(cb_clk);

        // Step 1: Assert pop_ready
        pop_ready_flag = 1;
        cb_clk.pop_ready <= pop_ready_flag;  // Non-blocking or blocking depends on your usage
        $display({"Time: %0t, INFO: test_PopDataRetrievalTransaction1 - pop_ready asserted."},
                   $time);

        // Example: We attempt 10 pops
        for (i = 0; i < 10; i++) begin
          // ---- Wait for pop_valid with a cycle limit (so we don't hang forever) ----
          int cycle_count = 0;
          cb_clk.push_valid <= 1;
          while ((cb_clk.pop_valid == 0) && (cycle_count < 100)) begin
            @(cb_clk);
            cycle_count++;
          end

          if (cb_clk.pop_valid == 0) begin
            $display({"Time: %0t, ERROR: Did not see pop_valid within 100 cycles for pop %0d."},
                       $time, i);
            test_failed = 1;
            break;
          end

          // Now pop_valid is asserted, capture data
          expected_pop_data = cb_clk.pop_data;
          $display({"Time: %0t, INFO: pop_valid asserted, pop_data=0x%h."}, $time, cb_clk.pop_data);

          // Check data
          if (cb_clk.pop_data !== expected_pop_data) begin
            $display({"Time: %0t, ERROR: Data mismatch. ", "Expected 0x%h, got 0x%h."}, $time,
                       expected_pop_data, cb_clk.pop_data);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: Data matched: 0x%h."}, $time, cb_clk.pop_data);
            // If we haven't failed yet, mark as passing so far
            if (test_failed != 1) test_failed = 0;
          end
        end

        // De-assert pop_ready after finishing
        pop_ready_flag = 0;
        cb_clk.pop_ready <= pop_ready_flag;

        // Final pass/fail message
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopDataRetrievalTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopDataRetrievalTransaction1"}, $time);
        end

        // If we got here, test is done, so disable the timeout thread
        disable timeout_thread;
      end
    join
  endtask

  task automatic test_ItemCountManagementTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_ItemCountManagementTransaction1. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Manage the count of items in the FIFO, updating the current and next item counts based on pop operations.

        // Local variables declaration
        int i;
        int test_failed = -1;
        logic [CountWidth-1:0] expected_items;
        logic [CountWidth-1:0] expected_items_next;

        // Initial setup
        expected_items = 0;
        expected_items_next = 0;

        // Wait for a clock cycle to ensure initial conditions are set
        @(cb_clk);

        // Monitor pop_ready and update items and items_next
        fork
          begin
            // Simulate pop operations and update expected values
            for (i = 0; i < Depth; i++) begin
              // Randomly decide if pop_ready is asserted
              cb_clk.pop_ready <= $urandom_range(0, 1);
              @(cb_clk);

              // Update expected_items based on pop_ready
              if (cb_clk.pop_ready && cb_clk.pop_valid) begin
                expected_items = expected_items - 1;
              end

              // Calculate expected_items_next
              if (cb_clk.pop_ready && cb_clk.pop_valid) begin
                expected_items_next = expected_items - 1;
              end else begin
                expected_items_next = expected_items;
              end

              // Check the DUT's items and items_next against expected values
              if (cb_clk.items !== expected_items) begin
                $display({"Time: %0t, ERROR: test_ItemCountManagementTransaction1 - Check failed. ",
                          "Expected items: %0d, got: %0d"}, $time, expected_items, items);
                test_failed = 1;
              end else begin
                $display({"Time: %0t, INFO: test_ItemCountManagementTransaction1 - Check passed. ",
                          "Expected items: %0d, observed items: %0d"}, $time, expected_items,
                           items);
                if (test_failed != 1) test_failed = 0;
              end

              if (cb_clk.items_next !== expected_items_next) begin
                $display({"Time: %0t, ERROR: test_ItemCountManagementTransaction1 - Check failed. ",
                          "Expected items_next: %0d, got: %0d"}, $time, expected_items_next,
                           items_next);
                test_failed = 1;
              end else begin
                $display({"Time: %0t, INFO: test_ItemCountManagementTransaction1 - Check passed. ",
                          "Expected items_next: %0d, observed items_next: %0d"}, $time,
                           expected_items_next, items_next);
                if (test_failed != 1) test_failed = 0;
              end
            end
          end
        join

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_ItemCountManagementTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_ItemCountManagementTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_RegisterPopOutputsControlTransaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RegisterPopOutputsControlTransaction1. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Manage the registration of pop outputs when `RegisterPopOutputs` is enabled, ensuring that pop data and valid signals are registered before being output, which may add an additional cycle of latency.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] expected_pop_data;
        logic expected_pop_valid;
        logic [Width-1:0] random_push_data;
        logic random_push_valid;
        logic random_pop_ready;
        localparam int Width = 8;  // Assuming Width is 8 for this example

        // Preconditions: Ensure RegisterPopOutputs is enabled
        if (RegisterPopOutputs != 1) begin
          $display({"Time: %0t, INFO: test_RegisterPopOutputsControlTransaction1 - ",
                    "RegisterPopOutputs is not enabled."}, $time);
          test_failed = 0;
        end else begin
          // Initial setup
          @(cb_clk);
          random_push_data  = $urandom_range(0, 2 ** Width - 1);
          random_push_valid = 1;
          random_pop_ready  = 1;

          // Apply stimulus
          cb_clk.push_data  <= random_push_data;
          cb_clk.push_valid <= random_push_valid;
          cb_clk.pop_ready  <= random_pop_ready;
          $display({"Time: %0t, INFO: test_RegisterPopOutputsControlTransaction1 - Driving ",
                    "push_data=0x%h, push_valid=%0b, pop_ready=%0b"}, $time, random_push_data,
                     random_push_valid, random_pop_ready);

          // Wait for one clock cycle to register outputs
          @(cb_clk);

          // Capture expected values after registration
          expected_pop_data  = random_push_data;
          expected_pop_valid = random_push_valid;

          // Check registered outputs
          if (
            cb_clk.pop_data !== expected_pop_data ||
            cb_clk.pop_valid !== expected_pop_valid
          ) begin
            $display(
                {"Time: %0t, ERROR: test_RegisterPopOutputsControlTransaction1 - Check failed. ",
                 "Expected pop_data=0x%h, pop_valid=%0b, got pop_data=0x%h, pop_valid=%0b"}, $time,
                  expected_pop_data, expected_pop_valid, pop_data, pop_valid);
            test_failed = 1;
          end else begin
            $display(
                {"Time: %0t, INFO: test_RegisterPopOutputsControlTransaction1 - Check passed. ",
                 "Expected pop_data=0x%h, pop_valid=%0b, observed pop_data=0x%h, pop_valid=%0b"},
                  $time, expected_pop_data, expected_pop_valid, pop_data, pop_valid);
            if (test_failed != 1) test_failed = 0;
          end

          // Reset stimulus
          @(cb_clk);
          cb_clk.push_valid <= 0;
          cb_clk.pop_ready  <= 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_RegisterPopOutputsControlTransaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_RegisterPopOutputsControlTransaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
