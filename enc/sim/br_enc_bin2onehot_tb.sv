// Copyright 2024 The Bedrock-RTL Authors
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

`timescale 1ns / 1ps

module br_enc_bin2onehot_tb;

  // Parameters
  parameter int NumValues = 5;
  localparam int BinWidth = $clog2(NumValues);

  // DUT
  logic clk;
  logic rst;
  logic [BinWidth-1:0] in;
  logic [NumValues-1:0] out;
  logic in_valid;
  // Instantiate the DUT
  br_enc_bin2onehot #(
      .NumValues(NumValues)
  ) dut (
      .clk,
      .rst,
      .in,
      .in_valid(in_valid),
      .out
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;  // Toggle clock every 5 ns (100 MHz)
  end

  // Test sequence
  logic [NumValues-1:0] expected_out;
  integer errors = 0;

  initial begin
    // Initialize inputs
    rst = 1;
    in  = 0;

    // Wait for global reset
    #20;
    rst = 0;

    // Apply test vectors for valid inputs
    for (int i = 0; i < NumValues; i++) begin
      in = i;
      in_valid = 1'b1;
      #10;

      // Calculate expected output
      expected_out = '0;
      expected_out[i] = 1'b1;

      // Compare actual output with expected output
      if (out !== expected_out) begin
        $error("Time: %0t | Input: %0d | Expected Output: %b | Actual Output: %b", $time, in,
               expected_out, out);
        errors = errors + 1;
      end else begin
        $display("Time: %0t | Input: %0d | Expected Output: %b | Actual Output: %b", $time, in,
                 expected_out, out);
      end
    end

    // Check that the DUT can handle invalid inputs
    in_valid = 1'b0;
    in = 'x;
    #10;
    if (out !== '0) begin
      $error("Time: %0t | Input: %0d | Expected Output: %b | Actual Output: %b", $time, in,
             '0, out);
      errors = errors + 1;
    end

    #10;

    // Finish simulation
    #10;

    // TODO(mgottscho): not enough information to know if test passed.
    // If DUT asserts fire, we can't see that here.
    // Need to determine pass/fail outside of this TB?
    if (errors) begin
      $display("Number of errors: %0d", errors);
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end

endmodule : br_enc_bin2onehot_tb
