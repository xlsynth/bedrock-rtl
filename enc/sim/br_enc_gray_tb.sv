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

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_enc_gray_tb;

  parameter int Width = 2;

  logic clk;
  logic rst;
  logic [Width-1:0] counter;
  logic [Width-1:0] counter_prev;
  logic [Width-1:0] counter_bin2gray;
  logic [Width-1:0] counter_gray2bin;
  logic [Width-1:0] counter_bin2gray_prev;

  br_enc_bin2gray #(
      .Width(Width)
  ) bin2gray (
      .bin (counter),
      .gray(counter_bin2gray)
  );

  br_enc_gray2bin #(
      .Width(Width)
  ) gray2bin (
      .gray(counter_bin2gray),
      .bin (counter_gray2bin)
  );

  `BR_REG(counter, counter + 1)
  `BR_REG(counter_bin2gray_prev, counter_bin2gray)

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;  // Toggle clock every 5 ns (100 MHz)
  end

  integer errors = 0;
  logic   result;

  // Test sequence
  initial begin
    rst = 1;
    @(negedge clk);
    @(negedge clk);
    rst = 0;

    // Wait until the counter satures
    while (counter != '1) begin
      if (counter != counter_gray2bin) begin
        $error("Time: %0t | Counter: %0h | Gray Output: %0h | Actual Output: %0h", $time, counter,
               counter_bin2gray, counter_gray2bin);
        errors = errors + 1;
      end

      result = counter_bin2gray ^ counter_bin2gray_prev;
      if (result != 0 && !br_math::is_power_of_2(result)) begin
        $error("Time: %0t | Counter: %0h | Gray Output: %2b | Previous Gray Output: %2b", $time,
               counter, counter_bin2gray, counter_bin2gray_prev);
        errors = errors + 1;
      end

      @(negedge clk);
    end

    if (errors) begin
      $display("Number of errors: %0d", errors);
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end

endmodule : br_enc_gray_tb
