//=============================================================
// Testbench for Module: br_enc_bin2gray
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_enc_bin2gray
//=============================================================

module tb;
  timeunit 1ns;
  timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  
  
  parameter TIMEOUT = 10000000;          // Timeout value in ns
  parameter PER_TASK_TIMEOUT = 1000000; // Timeout value for each task in ns
  parameter DRAIN_TIME = 10000;        // Time to observe all results in ns
  
  
  parameter DISABLE_CHECKS = 0;  // Disable checks
  
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
  logic[Width-1:0] bin;
  logic[Width-1:0] gray;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_bin2gray 
      #(
          .Width(Width)
      )  dut (
          .bin(bin),
          .gray(gray)
      );
      
  //===========================================================
  // Helper testbench variables
  //===========================================================
  int test_failed = -1;
          
  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
      
      #(TIMEOUT);
      $display("Error: Testbench timeout!");
      $finish;
  end
  
  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
      test_Transaction1();
  
    $finish;
  end

  
  task automatic test_Transaction1;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display("Time: %0t, INFO: Timeout: test_Transaction1. Stimuli is not observed or it needs more time to finish this test.", $time);
      end
      begin
          // Purpose: To verify the conversion of a binary input to its corresponding Gray code representation.
          
          // Local variables declaration
          int i;
          int test_failed = -1;
          logic [Width-1:0] expected_gray;
          logic [Width-1:0] bin_input;
          
          // Test different binary inputs and check the corresponding Gray code outputs
          for (i = 0; i < (1 << Width); i++) begin
            bin_input = i;
            expected_gray = (bin_input >> 1) ^ bin_input; // Calculate expected Gray code
            
            // Apply stimulus
            bin = bin_input;
            #1; // Delay to allow propagation
            
            // Display applied stimulus
            $display("Time: %0t, INFO: test_Transaction1 - Driving bin=0x%h", $time, bin_input);
            
            // Check the output
            if (gray !== expected_gray) begin
              $display("Time: %0t, ERROR: test_Transaction1 - Check failed. Expected gray=0x%h, got gray=0x%h", $time, expected_gray, gray);
              test_failed = 1;
            end else begin
              $display("Time: %0t, INFO: test_Transaction1 - Check passed. Expected gray=0x%h is the same as the observed gray=0x%h.", $time, expected_gray, gray);
              if (test_failed != 1)
                test_failed = 0;
            end
          end
          
          // Report test status
          if (test_failed == 0) begin
            $display("Time: %0t, PASSED: test_Transaction1", $time);
          end else begin
            $display("Time: %0t, FAILED: test_Transaction1", $time);
          end
      end
    join_any
    disable fork;
  endtask
  
endmodule
  
