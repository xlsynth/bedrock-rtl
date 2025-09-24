// SPDX-License-Identifier: Apache-2.0


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
    input out_valid, out;
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
    test_NormalConversion();

    reset_dut();
    test_SpecialCaseConversion();

    reset_dut();
    test_OneHotInput();

    reset_dut();
    test_InputAllZero();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_NormalConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_NormalConversion. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
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
            $display($sformatf({"Time: %0t, ERROR: test_NormalConversion - Check failed. ",
                                "Expected out=0x%h, out_valid=%b; got out=0x%h, out_valid=%b"},
                                 $time, expected_out, expected_out_valid, cb_clk.out,
                                 cb_clk.out_valid));
            test_failed = 1;
          end else begin
            $display($sformatf({"Time: %0t, INFO: test_NormalConversion - Check passed. ",
                                "Expected out=0x%h, out_valid=%b; observed out=0x%h, out_valid=%b."
                                 }, $time, expected_out, expected_out_valid, cb_clk.out,
                                 cb_clk.out_valid));
            if (test_failed != 1) test_failed = 0;
          end
        end

        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_NormalConversion", $time);
        end else begin
          $display("Time: %0t, FAILED: test_NormalConversion", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_SpecialCaseConversion;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_SpecialCaseConversion. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Handle the special case where all input bits are zero.
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
        $display($sformatf({"Time: %0t, INFO: test_SpecialCaseConversion - Driving in=0x%h"},
                             $time, in_signal));

        // Wait for the combinational logic to settle
        @(cb_clk);

        // Check outputs
        if (cb_clk.out_valid !== expected_out_valid || cb_clk.out !== expected_out) begin
          $display($sformatf({"Time: %0t, ERROR: test_SpecialCaseConversion - Check failed. ",
                              "Expected out_valid=%b, out=0x%h; got out_valid=%b, out=0x%h"}, $time,
                               expected_out_valid, expected_out, cb_clk.out_valid, cb_clk.out));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_SpecialCaseConversion - Check passed. ",
                              "Expected out_valid=%b, out=0x%h; observed out_valid=%b, out=0x%h"},
                               $time, expected_out_valid, expected_out, cb_clk.out_valid,
                               cb_clk.out));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_SpecialCaseConversion", $time);
        end else begin
          $display("Time: %0t, FAILED: test_SpecialCaseConversion", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

  task automatic test_OneHotInput;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_OneHotInput. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Verify output validity when a single bit in the input is set.
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
            $display($sformatf({"Time: %0t, ERROR: test_OneHotInput - Check failed for out_valid. ",
                                "Expected %b, got %b"}, $time, expected_out_valid, out_valid));
            test_failed = 1;
          end else begin
            $display($sformatf({"Time: %0t, INFO: test_OneHotInput - Check passed for out_valid. ",
                                "Expected value is the same as the observed value (both are %b)."},
                                 $time, out_valid));
            if (test_failed != 1) test_failed = 0;
          end

          // Check out
          if (cb_clk.out !== expected_out) begin
            $display($sformatf({"Time: %0t, ERROR: test_OneHotInput - Check failed for out. ",
                                "Expected %b, got %b"}, $time, expected_out, out));
            test_failed = 1;
          end else begin
            $display($sformatf({"Time: %0t, INFO: test_OneHotInput - Check passed for out. ",
                                "Expected value is the same as the observed value (both are %b)."},
                                 $time, out));
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_OneHotInput", $time);
        end else begin
          $display("Time: %0t, FAILED: test_OneHotInput", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_InputAllZero;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_InputAllZero. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Verify output validity when all input bits are zero.
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
        $display($sformatf({"Time: %0t, INFO: test_InputAllZero - Driving in=0x%h"}, $time,
                             in_signal));

        // Wait for the combinational logic to settle
        @(cb_clk);

        // Check the output validity
        if (cb_clk.out_valid !== out_valid_expected) begin
          $display($sformatf({"Time: %0t, ERROR: test_InputAllZero - Check failed. ",
                              "Expected out_valid=%0b, got out_valid=%0b"}, $time,
                               out_valid_expected, cb_clk.out_valid));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_InputAllZero - Check passed. ",
                        "Expected out_valid=%0b is the same as the observed value (both are %0b)."
                         }, $time, out_valid_expected, cb_clk.out_valid));
          if (test_failed != 1) test_failed = 0;
        end

        // Check the output value
        if (cb_clk.out !== out_expected) begin
          $display($sformatf({"Time: %0t, ERROR: test_InputAllZero - Check failed. ",
                              "Expected out=0x%h, got out=0x%h"}, $time, out_expected, cb_clk.out));
          test_failed = 1;
        end else begin
          $display($sformatf({"Time: %0t, INFO: test_InputAllZero - Check passed. ",
                              "Expected out=0x%h is the same as the observed value (both are 0x%h)."
                               }, $time, out_expected, cb_clk.out));
          if (test_failed != 1) test_failed = 0;
        end

        // Report test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_InputAllZero", $time);
        end else begin
          $display("Time: %0t, FAILED: test_InputAllZero", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
