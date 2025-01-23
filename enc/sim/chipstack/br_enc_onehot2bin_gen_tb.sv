//=============================================================
// Testbench for Module: br_enc_onehot2bin
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_enc_onehot2bin
//=============================================================

module br_enc_onehot2bin_gen_tb;
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
  parameter int BinWidth = $clog2(NumValues);

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [NumValues-1:0] in;
  logic out_valid;
  logic [BinWidth-1:0] out;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_onehot2bin #(
      .NumValues(NumValues),
      .BinWidth (BinWidth)
  ) dut (
      .clk(clk),
      .rst(rst),
      .in(in),
      .out_valid(out_valid),
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
    inout rst, in;
    input out_valid, out;
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
    test_NormalConversion();

    reset_dut();
    test_SpecialCaseConversion();

    reset_dut();
    test_IllegalInputHandling();

    reset_dut();
    test_Transaction1();

    reset_dut();
    test_Transaction2();

    $finish;
  end


  task automatic test_NormalConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_NormalConversion. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        int i;
        int test_failed = -1;
        logic [NumValues-1:0] test_in;
        logic [BinWidth-1:0] expected_out;
        logic expected_out_valid;

        for (i = 0; i < NumValues; i++) begin
          test_in = '0;
          test_in[i] = 1'b1;
          expected_out = BinWidth'(i);
          expected_out_valid = 1'b1;

          @(cb_clk);
          cb_clk.in <= test_in;

          @(cb_clk);

          if (cb_clk.out !== expected_out || cb_clk.out_valid !== expected_out_valid) begin
            $display({"Time: %0t, ERROR: test_NormalConversion - Check failed. ",
                      "Expected out=0x%h, out_valid=%b; got out=0x%h, out_valid=%b"}, $time,
                       expected_out, expected_out_valid, cb_clk.out, cb_clk.out_valid);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_NormalConversion - Check passed. ",
                      "Expected out=0x%h, out_valid=%b; observed out=0x%h, out_valid=%b."}, $time,
                       expected_out, expected_out_valid, cb_clk.out, cb_clk.out_valid);
            if (test_failed != 1) test_failed = 0;
          end
        end

        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_NormalConversion"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_NormalConversion"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_SpecialCaseConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_SpecialCaseConversion. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Handle the special case where all input bits are zero.
        // Local variables declaration
        int test_failed = -1;
        logic [NumValues-1:0] in_signal;
        logic [BinWidth-1:0] expected_out;
        logic expected_out_valid;

        // Initialize input signals
        in_signal = '0;
        expected_out = '0;
        expected_out_valid = 0;

        // Apply stimulus
        @(cb_clk);
        cb_clk.in <= in_signal;
        $display({"Time: %0t, INFO: test_SpecialCaseConversion - Driving in=0x%h"}, $time,
                   in_signal);

        // Wait for the combinational logic to settle
        @(cb_clk);

        // Check outputs
        if (cb_clk.out_valid !== expected_out_valid || cb_clk.out !== expected_out) begin
          $display({"Time: %0t, ERROR: test_SpecialCaseConversion - Check failed. ",
                    "Expected out_valid=%b, out=0x%h; got out_valid=%b, out=0x%h"}, $time,
                     expected_out_valid, expected_out, cb_clk.out_valid, cb_clk.out);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_SpecialCaseConversion - Check passed. ",
                    "Expected out_valid=%b, out=0x%h; observed out_valid=%b, out=0x%h"}, $time,
                     expected_out_valid, expected_out, cb_clk.out_valid, cb_clk.out);
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_SpecialCaseConversion"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_SpecialCaseConversion"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_IllegalInputHandling;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_IllegalInputHandling. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        int test_failed = -1;
        logic [NumValues-1:0] illegal_input;
        logic [BinWidth-1:0] expected_out;
        logic expected_out_valid;

        illegal_input = 'b00101;

        @(cb_clk);
        cb_clk.in <= illegal_input;
        $display({"Time: %0t, INFO: test_IllegalInputHandling - Driving illegal input in=0x%h"},
                   $time, illegal_input);

        @(cb_clk);

        expected_out = 'x;
        expected_out_valid = 'x;

        if (cb_clk.out !== expected_out || cb_clk.out_valid !== expected_out_valid) begin
          $display({"Time: %0t, ERROR: test_IllegalInputHandling - Check failed. ",
                    "Expected out=0x%x, out_valid=%b, got out=0x%x, out_valid=%b"}, $time,
                     expected_out, expected_out_valid, cb_clk.out, cb_clk.out_valid);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_IllegalInputHandling - Check passed. ",
                    "Expected values are undefined as observed."}, $time);
          if (test_failed != 1) test_failed = 0;
        end

        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_IllegalInputHandling"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_IllegalInputHandling"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_Transaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_Transaction1. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Verify output validity when a single bit in the input is set.
        // Local variables declaration
        int i;
        int test_failed = -1;
        logic [NumValues-1:0] test_in;
        logic [BinWidth-1:0] expected_out;
        logic expected_out_valid;

        // Precondition: Initialize test inputs
        test_in = '0;
        expected_out = '0;
        expected_out_valid = 0;

        // Apply stimulus and check results
        for (i = 0; i < NumValues; i++) begin
          @(cb_clk);
          test_in = '0;
          test_in[i] = 1'b1;  // Set a single bit
          expected_out = BinWidth'(i);
          expected_out_valid = 1'b1;

          // Apply input
          cb_clk.in <= test_in;

          @(cb_clk);
          // Check out_valid
          if (cb_clk.out_valid !== expected_out_valid) begin
            $display({"Time: %0t, ERROR: test_Transaction1 - Check failed for out_valid. ",
                      "Expected %b, got %b"}, $time, expected_out_valid, out_valid);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_Transaction1 - Check passed for out_valid. ",
                      "Expected value is the same as the observed value (both are %b)."}, $time,
                       out_valid);
            if (test_failed != 1) test_failed = 0;
          end

          // Check out
          if (cb_clk.out !== expected_out) begin
            $display({"Time: %0t, ERROR: test_Transaction1 - Check failed for out. ",
                      "Expected %b, got %b"}, $time, expected_out, out);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_Transaction1 - Check passed for out. ",
                      "Expected value is the same as the observed value (both are %b)."}, $time,
                       out);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_Transaction1"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_Transaction1"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_Transaction2;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_Transaction2. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // Purpose: Verify output validity when all input bits are zero.
        // Local variables declaration
        int test_failed = -1;
        logic [NumValues-1:0] in_signal;
        logic out_valid_expected;
        logic [BinWidth-1:0] out_expected;

        // Initialize input signal to all zeros
        in_signal = '0;
        out_valid_expected = 0;
        out_expected = '0;

        // Apply stimulus
        @(cb_clk);
        cb_clk.in <= in_signal;
        $display({"Time: %0t, INFO: test_Transaction2 - Driving in=0x%h"}, $time, in_signal);

        // Wait for the combinational logic to settle
        @(cb_clk);

        // Check the output validity
        if (cb_clk.out_valid !== out_valid_expected) begin
          $display({"Time: %0t, ERROR: test_Transaction2 - Check failed. ",
                    "Expected out_valid=%0b, got out_valid=%0b"}, $time, out_valid_expected,
                     cb_clk.out_valid);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_Transaction2 - Check passed. ",
                    "Expected out_valid=%0b is the same as the observed value (both are %0b)."},
                     $time, out_valid_expected, cb_clk.out_valid);
          if (test_failed != 1) test_failed = 0;
        end

        // Check the output value
        if (cb_clk.out !== out_expected) begin
          $display({"Time: %0t, ERROR: test_Transaction2 - Check failed. ",
                    "Expected out=0x%h, got out=0x%h"}, $time, out_expected, cb_clk.out);
          test_failed = 1;
        end else begin
          $display({"Time: %0t, INFO: test_Transaction2 - Check passed. ",
                    "Expected out=0x%h is the same as the observed value (both are 0x%h)."}, $time,
                     out_expected, cb_clk.out);
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_Transaction2"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_Transaction2"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
