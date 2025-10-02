// SPDX-License-Identifier: Apache-2.0


module br_enc_bin2gray_gen_tb;
  timeunit 1ns; timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  parameter int TIMEOUT = 10000000;  // Timeout value in ns
  parameter int PER_TASK_TIMEOUT = 1000000;  // Timeout value for each task in ns
  parameter int DRAIN_TIME = 10000;  // Time to observe all results in ns

  //===========================================================
  // DUT Imports and Includes
  //===========================================================

  `include "br_asserts_internal.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int Width = 2;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [Width-1:0] bin;
  logic [Width-1:0] gray;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_bin2gray #(
      .Width(Width)
  ) dut (
      .bin (bin),
      .gray(gray)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;

  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    #(TIMEOUT);
    $display($sformatf({"Error: Testbench timeout!"}));
    $finish;
  end

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
    test_Transaction1();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_Transaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_Transaction1. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: To verify the conversion of a binary input to its corresponding Gray code representation.

        int i;
        int test_failed = -1;
        logic [Width-1:0] expected_gray;
        logic [Width-1:0] bin_input;

        // Test different binary inputs and check the corresponding Gray code outputs
        for (i = 0; i < (1 << Width); i++) begin
          bin_input = i;
          expected_gray = (bin_input >> 1) ^ bin_input;  // Calculate expected Gray code

          // Apply stimulus
          bin = bin_input;
          #1;  // Delay to allow propagation

          // Display applied stimulus
          $display($sformatf({"Time: %0t, INFO: test_Transaction1 - Driving bin=0x%h"}, $time,
                               bin_input));

          // Check the output
          if (gray !== expected_gray) begin
            $display($sformatf({"Time: %0t, ERROR: test_Transaction1 - Check failed. ",
                                "Expected gray=0x%h, got gray=0x%h"}, $time, expected_gray, gray));
            test_failed = 1;
          end else begin
            $display($sformatf({"Time: %0t, INFO: test_Transaction1 - Check passed. ",
                                "Expected gray=0x%h is the same as the observed gray=0x%h."},
                                 $time, expected_gray, gray));
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Report test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_Transaction1"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_Transaction1"}, $time));
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
