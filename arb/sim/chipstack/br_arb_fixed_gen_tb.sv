//=============================================================
// Testbench for Module: br_arb_fixed
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_arb_fixed
//=============================================================

module br_arb_fixed_gen_tb;
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

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int NumRequesters = 2;

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [NumRequesters-1:0] request;
  logic [NumRequesters-1:0] grant;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_arb_fixed #(
      .NumRequesters(NumRequesters)
  ) dut (
      .clk(clk),
      .rst(rst),
      .request(request),
      .grant(grant)
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
    inout rst, request;
    input grant;
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
    cb_clk.request <= 'h0;

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
    test_RequestEvaluation();

    reset_dut();
    test_PriorityDetermination();

    reset_dut();
    test_LowestIndexPriority();

    reset_dut();
    test_SingleRequestGrant();

    reset_dut();
    test_GrantSignals();

    reset_dut();
    test_OnehotGrant();

    reset_dut();
    test_RequestAndGrantCorrelation();

    $finish;
  end


  task automatic test_RequestEvaluation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RequestEvaluation. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task evaluates the functionality of the fixed-priority arbiter by simulating multiple active requests and checking if the correct request is granted based on priority.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] request_val;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Initial setup
        request_val = '0;
        expected_grant = '0;

        // Wait for a clock cycle to ensure proper setup
        @(cb_clk);

        // Test multiple active requests
        for (i = 0; i < NumRequesters; i++) begin
          request_val[i] = 1'b1;  // Set the current cb_clk.request bit
          expected_grant = '0;
          expected_grant[i] = 1'b1;  // Expected cb_clk.grant is the current cb_clk.request bit

          // Apply stimulus
          cb_clk.request <= request_val;
          @(cb_clk);

          // Display the applied stimulus
          $display({"Time: %0t, INFO: test_RequestEvaluation - Driving request=0x%h"}, $time,
                     request_val);

          // Check the grant output
          if (cb_clk.grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_RequestEvaluation - Check failed. ",
                      "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_RequestEvaluation - Check passed. ",
                      "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                       expected_grant, grant);
            if (test_failed != 1) test_failed = 0;
          end

          // Reset request for next iteration
          request_val[i] = 1'b0;
          @(cb_clk);
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_RequestEvaluation"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_RequestEvaluation"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PriorityDetermination;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PriorityDetermination. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the priority determination functionality of the br_arb_fixed module.
        // It verifies that the arbiter grants the request with the highest priority (lowest index) when multiple requests are active.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Initialize request and expected_grant
        cb_clk.request <= '0;
        expected_grant = '0;

        // Apply multiple requests and check the grant output
        for (i = 0; i < NumRequesters; i++) begin
          // Set multiple bits in request to simulate simultaneous active requests
          cb_clk.request <= (1 << i) | (1 << (i + 1) % NumRequesters);
          expected_grant = 1 << i;  // Expect the lowest index cb_clk.request to be granted

          // Apply the request
          @(cb_clk);
          cb_clk.request <= request;
          $display({"Time: %0t, INFO: test_PriorityDetermination - Driving request=0x%h"}, $time,
                     request);

          // Check the grant output
          @(cb_clk);
          if (cb_clk.grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_PriorityDetermination - Check failed. ",
                      "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PriorityDetermination - Check passed. ",
                      "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                       expected_grant, grant);
            if (test_failed != 1) test_failed = 0;
          end

          // Introduce a random delay before the next iteration
          repeat ($urandom_range(1, 3)) @(cb_clk);
        end

        // Report the test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PriorityDetermination"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PriorityDetermination"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_LowestIndexPriority;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_LowestIndexPriority. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        int test_failed = -1;
        logic [NumRequesters-1:0] request_val;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        request_val = '0;
        request_val[0] = 1;

        // Corrected index to be within bounds
        if (NumRequesters > 2) begin
          request_val[2] = 1;
        end

        expected_grant = '0;
        expected_grant[0] = 1;

        @(cb_clk);
        cb_clk.request <= request_val;
        $display({"Time: %0t, INFO: test_LowestIndexPriority - Driving request=0x%h"}, $time,
                   request_val);

        @(cb_clk);

        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_LowestIndexPriority - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_LowestIndexPriority - Check passed. ",
                    "Expected value for grant is the same as the observed value (both are 0x%h)."},
                     $time, grant);
          if (test_failed != 1) test_failed = 0;
        end

        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_LowestIndexPriority"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_LowestIndexPriority"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_SingleRequestGrant;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_SingleRequestGrant. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the Single Request Grant functionality of the br_arb_fixed module.
        // It ensures that only one request is granted at a time, even when multiple requests are active.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] request_val;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Initial setup
        request_val = 0;
        expected_grant = 0;

        // Apply multiple requests
        request_val = 'b1011;  // Example: Requesters 0, 1, and 3 are active
        @(cb_clk);
        cb_clk.request <= request_val;
        $display({"Time: %0t, INFO: test_SingleRequestGrant - Driving request=0x%h"}, $time,
                   request_val);

        // Calculate expected grant
        for (i = 0; i < NumRequesters; i++) begin
          if (request_val[i]) begin
            expected_grant = 1 << i;
            break;
          end
        end

        // Wait for grant to stabilize
        @(cb_clk);

        // Check the grant output
        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_SingleRequestGrant - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_SingleRequestGrant - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, grant);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_SingleRequestGrant"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_SingleRequestGrant"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_GrantSignals;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_GrantSignals. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Task to verify the correct generation of grant signals based on active requests and their priorities.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] request_pattern;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Initial delay to ensure proper stimulus propagation
        @(cb_clk);

        // Test different request patterns
        for (i = 0; i < NumRequesters; i++) begin
          // Generate a request pattern with a single active request at position i
          request_pattern = 1 << i;
          expected_grant  = request_pattern;
          // Expected cb_clk.grant is the same as the cb_clk.request pattern for a single cb_clk.request

          // Apply the request pattern
          cb_clk.request <= request_pattern;
          @(cb_clk);

          // Check if the grant matches the expected value
          if (cb_clk.grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_GrantSignals - Check failed. ",
                      "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_GrantSignals - Check passed. ",
                      "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                       expected_grant, grant);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Test multiple requests with different priorities
        request_pattern = 'b1111;  // All requests active
        expected_grant  = 1;  // Only the highest priority (lowest index) should be granted

        // Apply the request pattern
        cb_clk.request <= request_pattern;
        @(cb_clk);

        // Check if the grant matches the expected value
        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_GrantSignals - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_GrantSignals - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, grant);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_GrantSignals"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_GrantSignals"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_OnehotGrant;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_OnehotGrant. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Verify that the `grant` signal is always one-hot encoded, meaning only one bit is set at any time.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] request_val;
        logic [NumRequesters-1:0] grant_val;
        int i;

        // Precondition: Ensure the system is in a known state
        @(cb_clk);
        request_val = 0;
        cb_clk.request <= request_val;
        @(cb_clk);

        // Test: Apply multiple requests and check the grant signal
        for (i = 0; i < NumRequesters; i = i + 1) begin
          request_val = (1 << i) | (1 << ((i + 1) % NumRequesters));
          // Set two bits in cb_clk.request
          cb_clk.request <= request_val;
          @(cb_clk);
          grant_val = cb_clk.grant;  // Capture the cb_clk.grant signal

          // Check if grant is one-hot encoded
          if (!$onehot0(grant_val)) begin
            $display({"Time: %0t, ERROR: test_OnehotGrant - Check failed. ",
                      "Grant is not one-hot. ", "Request: 0x%h, Grant: 0x%h"}, $time, request_val,
                       grant_val);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_OnehotGrant - Check passed. ", "Grant is one-hot. ",
                      "Request: 0x%h, Grant: 0x%h"}, $time, request_val, grant_val);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_OnehotGrant"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_OnehotGrant"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_RequestAndGrantCorrelation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RequestAndGrantCorrelation. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Verify that the `grant` signal correctly corresponds to the active `request` signal based on the fixed-priority scheme.

        // Local variables declaration
        int test_failed = -1;
        logic [NumRequesters-1:0] request_val;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Initial stimulus propagation delay
        @(cb_clk);

        // Test multiple scenarios of request and check grant correlation
        for (i = 0; i < NumRequesters; i++) begin
          // Set a single request bit
          request_val = 1 << i;
          expected_grant = 1 << i;

          // Apply the request
          cb_clk.request <= request_val;
          @(cb_clk);

          // Check if the grant corresponds to the request
          if (cb_clk.grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_RequestAndGrantCorrelation - Check failed. ",
                      "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_RequestAndGrantCorrelation - Check passed. ",
                      "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                       expected_grant, grant);
            if (test_failed != 1) test_failed = 0;
          end

          // Random delay between tests
          repeat ($urandom_range(1, 3)) @(cb_clk);
        end

        // Test multiple simultaneous requests
        request_val = '1;  // All cb_clk.request bits set
        expected_grant = 1;  // Only the lowest index should be granted

        // Apply the request
        cb_clk.request <= request_val;
        @(cb_clk);

        // Check if the grant corresponds to the highest priority request
        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RequestAndGrantCorrelation - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RequestAndGrantCorrelation - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, grant);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_RequestAndGrantCorrelation"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_RequestAndGrantCorrelation"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
