// SPDX-License-Identifier: Apache-2.0

module br_enc_bin2onehot_gen_tb;
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
  parameter int NumValues = 2;
  parameter int EnableInputRangeCheck = 1;
  parameter int BinWidth = $clog2(NumValues);

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [BinWidth-1:0] in;
  logic in_valid;
  logic [NumValues-1:0] out;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_bin2onehot #(
      .NumValues(NumValues),
      .EnableInputRangeCheck(EnableInputRangeCheck),
      .BinWidth(BinWidth)
  ) dut (
      .clk(clk),
      .rst(rst),
      .in(in),
      .in_valid(in_valid),
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
    inout rst, in, in_valid;
    input out;
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
    cb_clk.in <= 'h0;
    cb_clk.in_valid <= 'h0;

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
    test_BinaryToOnehotConversion();

    reset_dut();
    test_InvalidInputHandling();

    reset_dut();
    test_InputRangeValidationWithinRange();

    reset_dut();
    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_BinaryToOnehotConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_BinaryToOnehotConversion. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Convert a binary-encoded input to a onehot-encoded output when the input is valid.
        int i;
        int test_failed = -1;
        logic [NumValues-1:0] expected_out;
        logic [BinWidth-1:0] test_in;
        logic test_in_valid;

        // Precondition: Ensure initial state
        @(cb_clk);
        test_in_valid = 0;
        test_in = 0;
        expected_out = '0;

        // Test each valid binary input
        for (i = 0; i < NumValues; i++) begin
          @(cb_clk);
          test_in = i;
          test_in_valid = 1;
          expected_out = '0;
          expected_out[i] = 1'b1;
          cb_clk.in <= test_in;
          cb_clk.in_valid <= test_in_valid;

          @(cb_clk);
          @(cb_clk);
          if (cb_clk.out !== expected_out) begin
            $display($sformatf({"Time: %0t, ERROR: test_BinaryToOnehotConversion - Check failed. ",
                                "in=0x%h, in_valid=0x%h, Expected out=0x%h, got out=0x%h"}, $time,
                                 cb_clk.in, cb_clk.in_valid, expected_out, out));
            test_failed = 1;
          end else begin
            $display(
                $sformatf(
                    {"Time: %0t, INFO: test_BinaryToOnehotConversion - Check passed. ",
                     "Expected value for out is the same as the observed value (both are 0x%h)."},
                      $time, out));
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_BinaryToOnehotConversion", $time);
        end else begin
          $display("Time: %0t, FAILED: test_BinaryToOnehotConversion", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InvalidInputHandling;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_InvalidInputHandling. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Ensure that when the input is invalid, the output is driven to zero.

        int test_failed = -1;
        logic [BinWidth-1:0] random_in;
        logic random_in_valid;
        logic [NumValues-1:0] expected_out;

        // Initial setup
        expected_out = '0;

        // Apply stimulus
        @(cb_clk);
        random_in = $urandom_range(0, NumValues - 1);
        random_in_valid = 0;  // Deassert cb_clk.in_valid to indicate invalid input
        cb_clk.in <= random_in;
        cb_clk.in_valid <= random_in_valid;
        $display($sformatf({"Time: %0t, INFO: test_InvalidInputHandling - ",
                            "Driving in=0x%h, in_valid=%b"}, $time, random_in, random_in_valid));

        // Wait for the output to stabilize

        // Check the output
        if (cb_clk.out !== expected_out) begin
          $display($sformatf({"Time: %0t, ERROR: test_InvalidInputHandling - Check failed. ",
                              "Expected out=0x%h, got out=0x%h"}, $time, expected_out, cb_clk.out));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_InvalidInputHandling - Check passed. ",
                        "Expected value for out is the same as the observed value (both are 0x%h)."
                         }, $time, out));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_InvalidInputHandling", $time);
        end else begin
          $display("Time: %0t, FAILED: test_InvalidInputHandling", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InputRangeValidationWithinRange;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_InputRangeValidationWithinRange. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Check if the binary input is within the valid range specified by `NumValues` when `EnableInputRangeCheck` is enabled.

        int i;
        int test_failed = -1;
        logic [BinWidth-1:0] test_in;
        logic test_in_valid;
        logic [NumValues-1:0] expected_out;

        // Precondition: Ensure the DUT is in a known state
        @(cb_clk);
        test_in = 0;
        test_in_valid = 0;
        expected_out = 0;

        // Apply stimulus and check output
        for (i = 0; i < NumValues; i++) begin
          @(cb_clk);
          test_in = i;
          test_in_valid = 1;
          expected_out = '0;
          expected_out[i] = 1'b1;

          // Apply stimulus
          cb_clk.in <= test_in;
          cb_clk.in_valid <= test_in_valid;

          @(cb_clk);
          // Check if the output matches the expected onehot encoding
          if (cb_clk.out !== expected_out) begin
            $display($sformatf({"Time: %0t, ERROR: test_InputRangeValidationWithinRange - ",
                                "Check failed. Expected out=0x%h, got out=0x%h"}, $time,
                                 expected_out, cb_clk.out));
            test_failed = 1;
          end else begin
            $display(
                $sformatf(
                    {"Time: %0t, INFO: test_InputRangeValidationWithinRange - Check passed. ",
                     "Expected value for out is the same as the observed value (both are 0x%h)."},
                      $time, out));
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_InputRangeValidationWithinRange", $time);
        end else begin
          $display("Time: %0t, FAILED: test_InputRangeValidationWithinRange", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
