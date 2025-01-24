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

module br_arb_lru_gen_tb;
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
  parameter int NumRequesters = 2;

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
  br_arb_lru #(
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
    test_RequestGrantWithPriorityUpdate();

    reset_dut();
    test_RequestGrantWithoutPriorityUpdate();

    if (test_failed) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_RequestGrantWithPriorityUpdate;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RequestGrantWithPriorityUpdate. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Ensure that a request is granted based on the least-recently-used policy, with priority state updates.

        // Local variables declaration
        logic [NumRequesters-1:0] request_pattern;
        logic [NumRequesters-1:0] expected_grant;
        logic [NumRequesters-1:0] observed_grant;
        int i;

        // Initialize the testbench environment
        @(cb_clk);
        cb_clk.enable_priority_update <= 1;  // Enable priority updates
        cb_clk.request <= 0;  // Initialize cb_clk.request to zero
        @(cb_clk);

        // Step 1: Set multiple active requests
        request_pattern = 4'b1010;  // Example pattern with requests from 2nd and 4th requesters
        cb_clk.request <= request_pattern;
        $display({"Time: %0t, INFO: test_RequestGrantWithPriorityUpdate - Driving request=0x%b"},
                   $time, request_pattern);
        @(cb_clk);

        // Step 2: Evaluate the current priority state
        // Assuming the initial state grants the least recently used, which is the 2nd requester in this case
        expected_grant = 4'b0010;  // Expecting the 2nd requester to be granted
        observed_grant = cb_clk.grant;
        $display({"Time: %0t, INFO: test_RequestGrantWithPriorityUpdate - Observed grant=0x%b"},
                   $time, observed_grant);

        // Step 3: Check if the correct request is granted
        if (observed_grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RequestGrantWithPriorityUpdate - Check failed. ",
                    "Expected grant=0x%b, got grant=0x%b"}, $time, expected_grant, observed_grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RequestGrantWithPriorityUpdate - Check passed. ",
                    "Expected grant=0x%b is the same as the observed grant=0x%b."}, $time,
                     expected_grant, observed_grant);
          if (test_failed != 1) test_failed = 0;
        end

        // Step 4: Update priority state and check subsequent grants
        for (i = 0; i < NumRequesters; i++) begin
          @(cb_clk);
          cb_clk.request <= request_pattern;  // Maintain the same cb_clk.request pattern
          // Start of manual fix
          expected_grant = 4'b0010;
          // end of manual fix
          observed_grant = cb_clk.grant;
          $display({"Time: %0t, INFO: test_RequestGrantWithPriorityUpdate - Observed grant=0x%b"},
                     $time, observed_grant);

          if (observed_grant !== expected_grant) begin
            $display({"Time: %0t, ERROR: test_RequestGrantWithPriorityUpdate - Check failed. ",
                      "Expected grant=0x%b, got grant=0x%b"}, $time, expected_grant,
                       observed_grant);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_RequestGrantWithPriorityUpdate - Check passed. ",
                      "Expected grant=0x%b is the same as the observed grant=0x%b."}, $time,
                       expected_grant, observed_grant);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_RequestGrantWithPriorityUpdate"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_RequestGrantWithPriorityUpdate"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_RequestGrantWithoutPriorityUpdate;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_RequestGrantWithoutPriorityUpdate. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Ensure that a request is granted based on the least-recently-used policy, without updating the priority state.

        // Local variables declaration
        logic [NumRequesters-1:0] request_pattern;
        logic [NumRequesters-1:0] expected_grant;
        logic [NumRequesters-1:0] observed_grant;

        // Initialize request pattern and expected grant
        request_pattern = 'b1010;  // Example pattern with multiple active requests
        expected_grant  = 'b0010;  // Assuming the second requester is the least recently used

        // Apply initial conditions
        @(cb_clk);
        cb_clk.enable_priority_update <= 0;  // Disable priority update
        cb_clk.request <= request_pattern;

        // Wait for the design to process the request
        @(cb_clk);

        // Capture the observed grant output
        observed_grant = cb_clk.grant;

        // Check if the observed grant matches the expected grant
        if (observed_grant !== expected_grant) begin
          $display({"Time: %0t, ERROR: test_RequestGrantWithoutPriorityUpdate - Check failed. ",
                    "Expected grant: 0x%h, got: 0x%h"}, $time, expected_grant, observed_grant);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_RequestGrantWithoutPriorityUpdate - Check passed. ",
                    "Expected grant: 0x%h is the same as the observed grant: 0x%h."}, $time,
                     expected_grant, observed_grant);
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_RequestGrantWithoutPriorityUpdate"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_RequestGrantWithoutPriorityUpdate"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
