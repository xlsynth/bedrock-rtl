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

module br_enc_countones_gen_tb;
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
  parameter int Width = 10;
  localparam int CountWidth = $clog2((Width + 1));

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic [Width-1:0] in;
  logic [CountWidth-1:0] count;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_enc_countones #(
      .Width(Width)
  ) dut (
      .in(in),
      .count(count)
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
    test_CountOnesInInputVector();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_CountOnesInInputVector;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_CountOnesInInputVector. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
        overall_tb_status = 1'b0;
      end
      begin
        // Purpose: Verify the functionality of counting the number of '1's in the input vector `in`.

        int i;
        int test_failed = -1;
        logic [Width-1:0] test_input;
        logic [CountWidth-1:0] expected_count;
        logic [CountWidth-1:0] observed_count;

        // Test with various input vectors
        // Test case 1: All bits '0'
        test_input = '0;
        expected_count = 0;
        in = test_input;
        #1;  // Allow time for the DUT to process the input
        observed_count = count;
        if (observed_count !== expected_count) begin
          $display($sformatf({"Time: %0t, ERROR: test_CountOnesInInputVector - Check failed. ",
                              "Expected %0d, got %0d"}, $time, expected_count, observed_count));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_CountOnesInInputVector - Check passed. ",
                        "Expected value for count is the same as the observed value (both are %0d)."
                         }, $time, observed_count));
          if (test_failed != 1) test_failed = 0;
        end

        // Test case 2: All bits '1'
        test_input = '1;
        expected_count = Width;
        in = test_input;
        #1;
        observed_count = count;
        if (observed_count !== expected_count) begin
          $display($sformatf({"Time: %0t, ERROR: test_CountOnesInInputVector - Check failed. ",
                              "Expected %0d, got %0d"}, $time, expected_count, observed_count));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_CountOnesInInputVector - Check passed. ",
                        "Expected value for count is the same as the observed value (both are %0d)."
                         }, $time, observed_count));
          if (test_failed != 1) test_failed = 0;
        end

        // Test case 3: Random input vector
        test_input = $urandom_range(0, (1 << Width) - 1);
        expected_count = 0;
        for (i = 0; i < Width; i++) begin
          expected_count += test_input[i];
        end
        in = test_input;
        #1;
        observed_count = count;
        if (observed_count !== expected_count) begin
          $display($sformatf({"Time: %0t, ERROR: test_CountOnesInInputVector - Check failed. ",
                              "Expected %0d, got %0d"}, $time, expected_count, observed_count));
          test_failed = 1;
        end else begin
          $display($sformatf(
                       {"Time: %0t, INFO: test_CountOnesInInputVector - Check passed. ",
                        "Expected value for count is the same as the observed value (both are %0d)."
                         }, $time, observed_count));
          if (test_failed != 1) test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display($sformatf({"Time: %0t, PASSED: test_CountOnesInInputVector"}, $time));
        end else begin
          $display($sformatf({"Time: %0t, FAILED: test_CountOnesInInputVector"}, $time));
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
