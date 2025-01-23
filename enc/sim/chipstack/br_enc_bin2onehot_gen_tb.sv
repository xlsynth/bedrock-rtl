//=============================================================
// Testbench for Module: br_enc_bin2onehot
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_enc_bin2onehot
//=============================================================

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
    inout rst, in, in_valid;
    input out;
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
    cb_clk.in <= 'h0;
    cb_clk.in_valid <= 'h0;

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
    test_BinaryToOnehotConversion();

    reset_dut();
    test_InvalidInputHandling();

    reset_dut();
    test_InputRangeValidationWithinRange();

    reset_dut();
    test_InputRangeValidationOutOfRange();

    $finish;
  end


  task automatic test_BinaryToOnehotConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_BinaryToOnehotConversion.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Convert a binary-encoded input to a onehot-encoded output when the input is valid.
        // Local variables declaration
        int i;
        int test_failed = -1;
        localparam int NumValues = 5;
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

          @(cb_clk);
          if (cb_clk.out !== expected_out) begin
            $display({"Time: %0t, ERROR: test_BinaryToOnehotConversion - Check failed.",
                      "Expected out=0x%h, got out=0x%h"}, $time, expected_out, out);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_BinaryToOnehotConversion - Check passed.",
                      "Expected value for out is the same as the observed value (both are 0x%h)."},
                       $time, out);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Test invalid input scenario
        @(cb_clk);
        test_in = NumValues;  // Invalid input
        test_in_valid = 1;
        expected_out = '0;

        @(cb_clk);
        if (cb_clk.out !== expected_out) begin
          $display({"Time: %0t, ERROR: test_BinaryToOnehotConversion - Check failed for invalid",
                    "input.", "Expected out=0x%h, got out=0x%h"}, $time, expected_out, out);
          test_failed = 1;
        end else begin
          $display(
              {"Time: %0t, INFO: test_BinaryToOnehotConversion - Check passed for invalid input.",
               "Expected value for out is the same as the observed value (both are 0x%h)."}, $time,
                out);
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_BinaryToOnehotConversion"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_BinaryToOnehotConversion"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InvalidInputHandling;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_InvalidInputHandling.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Ensure that when the input is invalid, the output is driven to zero.

        // Local variables declaration
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
        $display({"Time: %0t, INFO: test_InvalidInputHandling - Driving in=0x%h, in_valid=%b"},
                   $time, random_in, random_in_valid);

        // Wait for the output to stabilize
        @(cb_clk);

        // Check the output
        if (cb_clk.out !== expected_out) begin
          $display({"Time: %0t, ERROR: test_InvalidInputHandling - Check failed.",
                    "Expected out=0x%h, got out=0x%h"}, $time, expected_out, out);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_InvalidInputHandling - Check passed.",
                    "Expected value for out is the same as the observed value (both are 0x%h)."},
                     $time, out);
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_InvalidInputHandling"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_InvalidInputHandling"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InputRangeValidationWithinRange;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_InputRangeValidationWithinRange.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Check if the binary input is within the valid range specified by `NumValues` when `EnableInputRangeCheck` is enabled.

        // Local variables declaration
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
            $display({"Time: %0t, ERROR: test_InputRangeValidationWithinRange - Check failed.",
                      "Expected out=0x%h, got out=0x%h"}, $time, expected_out, out);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_InputRangeValidationWithinRange - Check passed.",
                      "Expected value for out is the same as the observed value (both are 0x%h)."},
                       $time, out);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_InputRangeValidationWithinRange"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_InputRangeValidationWithinRange"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InputRangeValidationOutOfRange;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_InputRangeValidationOutOfRange.",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Ensure that the input does not exceed the allowed range, preventing undefined behavior.
        // Local variables declaration
        int test_failed = -1;
        localparam int NumValues = 5;  // Example value, should match the DUT configuration
        logic [NumValues-1:0] expected_out;
        logic [ BinWidth-1:0] invalid_in;

        // Generate an invalid input value outside the range [0, NumValues-1]
        invalid_in = NumValues + $urandom_range(1, 10);  // Ensure it's cb_clk.out of range

        // Apply stimulus
        @(cb_clk);
        cb_clk.in <= invalid_in;
        cb_clk.in_valid <= 1'b1;
        $display({"Time: %0t, INFO: test_InputRangeValidationOutOfRange - Driving in=0x%h,",
                  "in_valid=1"}, $time, invalid_in);

        // Wait for the output to stabilize
        @(cb_clk);

        // Check the output
        expected_out = '0;  // Expected output is zero for cb_clk.out-of-range input
        if (cb_clk.out !== expected_out) begin
          $display({"Time: %0t, ERROR: test_InputRangeValidationOutOfRange - Check failed.",
                    "Expected out=0x%h, got out=0x%h"}, $time, expected_out, out);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_InputRangeValidationOutOfRange - Check passed.",
                    "Expected value for out is the same as the observed value (both are 0x%h)."},
                     $time, out);
          if (test_failed != 1) test_failed = 0;
        end

        // Disable further stimulus
        @(cb_clk);
        cb_clk.in_valid <= 1'b0;

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_InputRangeValidationOutOfRange"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_InputRangeValidationOutOfRange"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
