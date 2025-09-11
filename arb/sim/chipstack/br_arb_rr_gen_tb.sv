// SPDX-License-Identifier: Apache-2.0

module br_arb_rr_gen_tb;
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
  parameter int NumRequesters = 4;

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic enable_priority_update;
  logic [NumRequesters-1:0] request;
  logic [NumRequesters-1:0] grant;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_arb_rr #(
      .NumRequesters(NumRequesters)
  ) dut (
      .clk(clk),
      .rst(rst),
      .enable_priority_update(enable_priority_update),
      .request(request),
      .grant(grant)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  int test_failed = 0;

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, enable_priority_update, request;
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
    cb_clk.enable_priority_update <= 'h0;
    cb_clk.request <= 'h0;

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
    test_RoundRobinPriorityUpdate();

    reset_dut();
    test_RequestEvaluation();

    reset_dut();
    test_GrantAssertion();

    if (test_failed) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_RoundRobinPriorityUpdate;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RoundRobinPriorityUpdate. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: To verify the round-robin priority update mechanism ensuring fair access among requesters.

        // Local variables declaration
        logic [NumRequesters-1:0] expected_grant;
        int current_priority = 0;

        // Initialize test conditions
        cb_clk.request <= 4'b0000;
        cb_clk.enable_priority_update <= 1'b0;
        expected_grant = 4'b0000;

        @(cb_clk);  // Ensure adequate stimulus propagation time

        // Step 1: Set initial requests
        cb_clk.request <= 4'b1010;  // Requesters 1 and 3 are making requests
        cb_clk.enable_priority_update <= 1'b1;  // Enable priority update
        expected_grant = 4'b0010;
        @(cb_clk);  // Wait for clock edge

        // Step 2: Check grant for the highest priority requester
        $display({"Time: %0t, INFO: test_RoundRobinPriorityUpdate - Driving request=0x%h, ",
                  "enable_priority_update=%b"}, $time, cb_clk.request,
                   cb_clk.enable_priority_update);
        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RoundRobinPriorityUpdate - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, cb_clk.grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RoundRobinPriorityUpdate - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, cb_clk.grant);
        end

        cb_clk.request <= 4'b1010;  // Keep the same cb_clk.request pattern
        cb_clk.enable_priority_update <= 1'b1;  // Enable priority update
        expected_grant = 4'b1000;  // Expecting requester 3 to be granted after rotation
        @(cb_clk);  // Wait for clock edge

        // Step 3: Rotate priority and check next grant
        $display({"Time: %0t, INFO: test_RoundRobinPriorityUpdate - Driving request=0x%h, ",
                  "enable_priority_update=%b"}, $time, cb_clk.request,
                   cb_clk.enable_priority_update);
        if (cb_clk.grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RoundRobinPriorityUpdate - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, cb_clk.grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RoundRobinPriorityUpdate - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, cb_clk.grant);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_RequestEvaluation;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RequestEvaluation. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: To evaluate incoming requests and determine which requester should be granted access based on the current priority.

        // Local variables declaration
        logic [NumRequesters-1:0] request_pattern;
        logic [NumRequesters-1:0] expected_grant;
        logic [NumRequesters-1:0] observed_grant;

        // Initial setup
        @(cb_clk);
        cb_clk.enable_priority_update <= 1;  // Enable priority update for fairness

        // Step 1: Set `request` to indicate which requesters are making requests
        request_pattern = 4'b1010;  // Example pattern: requesters 1 and 3 are requesting
        cb_clk.request <= request_pattern;
        $display({"Time: %0t, INFO: test_RequestEvaluation - Driving request=0x%h"}, $time,
                   request_pattern);

        // Step 2: Wait for the design to evaluate the `request` signals
        @(cb_clk);

        // Step 3: Determine the expected grant based on the current round-robin state
        // Assuming initial priority is with requester 0, and requester 1 should be granted
        expected_grant = 4'b0010;  // Expected cb_clk.grant for requester 1

        // Step 4: Capture the observed `grant` signal
        observed_grant = cb_clk.grant;
        $display({"Time: %0t, INFO: test_RequestEvaluation - Observed grant=0x%h"}, $time,
                   observed_grant);

        // Step 5: Verify that the correct requester is granted access
        if (observed_grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RequestEvaluation - Check failed. ",
                    "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, observed_grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RequestEvaluation - Check passed. ",
                    "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                     expected_grant, observed_grant);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_GrantAssertion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_GrantAssertion. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: To assert the grant signal for the requester with the highest priority, allowing it to proceed with its operation.

        // Local variables declaration
        logic [NumRequesters-1:0] request_pattern;
        logic [NumRequesters-1:0] expected_grant;
        int i;

        // Precondition: Ensure reset is applied
        @(cb_clk);
        cb_clk.rst <= 1;
        @(cb_clk);
        cb_clk.rst <= 0;

        // Test scenario: Apply request patterns and verify grant assertion
        for (i = 0; i < NumRequesters; i++) begin
          // Generate a request pattern with a single requester making a request
          request_pattern = 1 << i;
          expected_grant  = request_pattern;
          // Expected cb_clk.grant is the same as the cb_clk.request pattern

          // Apply the request pattern
          @(cb_clk);
          cb_clk.request <= request_pattern;
          cb_clk.enable_priority_update <= 1;  // Enable priority update

          // Wait for the grant to be asserted
          @(cb_clk);

          // Check if the grant matches the expected value
          if (cb_clk.grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_GrantAssertion - Check failed. ",
                      "Expected grant=0x%h, got grant=0x%h"}, $time, expected_grant, grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_GrantAssertion - Check passed. ",
                      "Expected grant=0x%h is the same as the observed grant=0x%h."}, $time,
                       expected_grant, grant);
          end
        end
      end
    join_any
    disable fork;
  endtask

endmodule
