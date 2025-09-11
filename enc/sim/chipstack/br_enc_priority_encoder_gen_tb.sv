// SPDX-License-Identifier: Apache-2.0

module br_enc_priority_encoder_gen_tb;
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
  `include "br_unused.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int NumRequesters = 2;
  parameter int NumResults = 1;

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [NumRequesters-1:0] in;
  logic [NumResults-1:0][NumRequesters-1:0] out;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters),
      .NumResults(NumResults)
  ) dut (
      .clk(clk),
      .rst(rst),
      .in (in),
      .out(out)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, in;
    input out;
  endclocking


  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    if (NO_ASSERTS_ON_RESET) $assertoff;
    #(TIMEOUT);
    $display($sformatf({"Error: Testbench timeout!"}));
    $finish;
  end

  //===========================================================
  // Reset Generation
  //===========================================================
  task automatic reset_dut;
    if (NO_ASSERTS_ON_RESET) $assertoff;
    // Set all the DUT inputs to zero, making sure there are no X/Z at the inputs.
    cb_clk.in <= 'h0;

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
    test_HighestPrioritySelection();

    reset_dut();
    test_MaskingLowerPriorities();

    reset_dut();
    test_OneHotEncoding();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_HighestPrioritySelection;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_HighestPrioritySelection. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Verify that the DUT correctly identifies and outputs the highest priority active request from the input signals, where the lowest index has the highest priority.

        int test_failed = -1;
        logic [NumRequesters-1:0] in_vector;
        logic [NumRequesters-1:0] expected_out;
        int i;

        // Initial stimulus
        in_vector = $urandom_range(0, (1 << NumRequesters) - 1);
        expected_out = '0;

        // Determine expected output based on highest priority active request
        for (i = 0; i < NumRequesters; i++) begin
          if (in_vector[i]) begin
            expected_out[i] = 1;
            break;
          end
        end

        // Apply stimulus
        @(cb_clk);
        cb_clk.in <= in_vector;
        $display($sformatf({"Time: %0t, INFO: test_HighestPrioritySelection - Driving in=0x%h"},
                             $time, in_vector));

        // Wait for the output to stabilize
        @(cb_clk);

        // Check the output
        if (cb_clk.out[0] !== expected_out) begin
          $display($sformatf({"Time: %0t, ERROR: test_HighestPrioritySelection - Check failed. ",
                              "Expected out[0]=0x%h, got out[0]=0x%h"}, $time, expected_out,
                               cb_clk.out[0]));
          test_failed = 1;
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_HighestPrioritySelection - Check passed. ",
                   "Expected value for out[0] is the same as the observed value (both are 0x%h)."},
                    $time, expected_out));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_HighestPrioritySelection"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_HighestPrioritySelection"}, $time));
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_MaskingLowerPriorities;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_MaskingLowerPriorities. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Ensure that the DUT masks all lower priority requests once a higher priority request has been identified and outputted.
        int test_failed = -1;
        logic [NumRequesters-1:0] in_vector;
        logic [NumResults-1:0][NumRequesters-1:0] expected_out;
        int i;

        // Initialize input vector with a specific pattern to test masking
        in_vector = 4'b1010;  // Example pattern where the highest priority is at index 1

        // Apply stimulus
        @(cb_clk);
        cb_clk.in <= in_vector;
        $display($sformatf({"Time: %0t, INFO: test_MaskingLowerPriorities - Driving in=0x%h"},
                             $time, in_vector));

        // Calculate expected output
        expected_out[0] = 4'b0010;  // Highest priority request is at index 1
        for (i = 1; i < NumResults; i++) begin
          expected_out[i] = 4'b0000;
          // No other requests should be active cb_clk.in subsequent outputs
        end

        // Wait for the DUT to process the input
        @(cb_clk);

        // Check the output
        if (cb_clk.out[0] !== expected_out[0]) begin
          $display($sformatf(
                       {"Time: %0t, ERROR: test_MaskingLowerPriorities - Check failed for out[0]. ",
                        "Expected 0x%h, got 0x%h"}, $time, expected_out[0], out[0]));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_MaskingLowerPriorities - Check passed for out[0]. ",
                        "Expected and observed value is 0x%h"}, $time, out[0]));
          if (test_failed != 1) test_failed = 0;
        end

        for (i = 1; i < NumResults; i++) begin
          if (cb_clk.out[i] !== expected_out[i]) begin
            $display(
                $sformatf(
                    {"Time: %0t, ERROR: test_MaskingLowerPriorities - Check failed for out[%0d]. ",
                     "Expected 0x%h, got 0x%h"}, $time, i, expected_out[i], out[i]));
            test_failed = 1;
          end else begin
            $display(
                $sformatf(
                    {"Time: %0t, INFO: test_MaskingLowerPriorities - Check passed for out[%0d]. ",
                     "Expected and observed value is 0x%h"}, $time, i, out[i]));
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Report test result
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_MaskingLowerPriorities"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_MaskingLowerPriorities"}, $time));
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_OneHotEncoding;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_OneHotEncoding. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Validate that the DUT produces a one-hot encoded output for each of the highest priority requests, up to the number specified by `NumResults`.

        int test_failed = -1;
        logic [NumRequesters-1:0] in_vector;
        logic [NumResults-1:0][NumRequesters-1:0] expected_out;
        int i, j;

        // Initialize input vector and expected output
        in_vector = '0;
        expected_out = '0;

        // Apply stimulus and check results
        @(cb_clk);
        for (i = 0; i < NumRequesters; i++) begin
          in_vector[i] = 1'b1;
          expected_out[0] = 1 << i;

          // Apply input
          cb_clk.in <= in_vector;
          @(cb_clk);

          // Check first result
          if (cb_clk.out[0] !== expected_out[0]) begin
            $display($sformatf({"Time: %0t, ERROR: test_OneHotEncoding - Check failed for out[0]. ",
                                "Expected 0x%h, got 0x%h"}, $time, expected_out[0], out[0]));
            test_failed = 1;
          end else begin
            $display($sformatf({"Time: %0t, INFO: test_OneHotEncoding - Check passed for out[0]. ",
                                "Expected and observed value: 0x%h"}, $time, out[0]));
            if (test_failed != 1) test_failed = 0;
          end

          // Check additional results if NumResults > 1
          for (j = 1; j < NumResults; j++) begin
            expected_out[j] = 1 << (i + j);
            if (cb_clk.out[j] !== expected_out[j]) begin
              $display($sformatf(
                           {"Time: %0t, ERROR: test_OneHotEncoding - Check failed for out[%0d]. ",
                            "Expected 0x%h, got 0x%h"}, $time, j, expected_out[j], out[j]));
              test_failed = 1;
            end else begin
              $display($sformatf(
                           {"Time: %0t, INFO: test_OneHotEncoding - Check passed for out[%0d]. ",
                            "Expected and observed value: 0x%h"}, $time, j, out[j]));
              if (test_failed != 1) test_failed = 0;
            end
          end

          // Reset input vector for next iteration
          in_vector[i] = 1'b0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_OneHotEncoding"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_OneHotEncoding"}, $time));
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
