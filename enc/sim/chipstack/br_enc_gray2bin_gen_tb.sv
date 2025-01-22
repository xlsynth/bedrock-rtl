//=============================================================
// Testbench for Module: br_enc_gray2bin
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_enc_gray2bin
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
  logic[Width-1:0] gray;
  logic[Width-1:0] bin;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_gray2bin 
      #(
          .Width(Width)
      )  dut (
          .gray(gray),
          .bin(bin)
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
    // Purpose: Convert a Gray code input to its equivalent binary representation using bitwise operations.
    
    // Local variables declaration
    int i;
    int test_failed = -1;
    logic [Width-1:0] gray_input;
    logic [Width-1:0] expected_bin_output;
    logic [Width-1:0] observed_bin_output;
    
    // Generate random Gray code input
    gray_input = $urandom_range(0, (1 << Width) - 1);
    
    // START OF MANUAL FIX
    // Calculate expected binary output using bitwise operations
    // expected_bin_output[Width-1] = gray_input[Width-1];
    // for (i = Width - 2; i >= 0; i--) begin
    //   expected_bin_output[i] = ^gray_input[Width-1:i];
    // end


    expected_bin_output[Width-1] = gray_input[Width-1]; // MSB remains the same
    for (int i = Width - 2; i >= 0; i--) begin
        expected_bin_output[i] = expected_bin_output[i + 1] ^ gray_input[i]; // XOR with the next bit
    end
    // END OF MANUAL FIX

    // Apply stimulus to the DUT
    gray = gray_input;
    #1; // Allow time for propagation
    
    // Capture the observed output from the DUT
    observed_bin_output = bin;
    
    // Display the applied stimulus
    $display("Time: %0t, INFO: test_Transaction1 - Driving gray=0x%h", $time, gray_input);
    
    // Perform check
    if (observed_bin_output !== expected_bin_output) begin
      $display("Time: %0t, ERROR: test_Transaction1 - Check failed. Expected bin=0x%h, got bin=0x%h", $time, expected_bin_output, observed_bin_output);
      test_failed = 1;
    end else begin
      $display("Time: %0t, INFO: test_Transaction1 - Check passed. Expected value for bin is the same as the observed value (both are 0x%h).", $time, expected_bin_output);
      if (test_failed != 1)
        test_failed = 0;
    end
    
    // Report test status
    if (test_failed == 0) begin
      $display("Time: %0t, PASSED: test_Transaction1", $time);
    end else begin
      $display("Time: %0t, FAILED: test_Transaction1", $time);
    end
  endtask
  
endmodule

