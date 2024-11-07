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

// Unit test for br_asserts.svh macros

`timescale 1ns / 1ps

`include "br_asserts.svh"

// verilog_lint: waive package-filename
package br_asserts_test_pkg;
  localparam int Width = 4;
  `BR_ASSERT_STATIC_IN_PACKAGE(width_check_a, Width == 4)
endpackage : br_asserts_test_pkg

module br_asserts_test;

  logic clk;
  logic rst;

  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic valid;

  // Reference the br_asserts_test_pkg so that the package is elaborated
  localparam int Width = br_asserts_test_pkg::Width;

  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst = 1;
    a = 0;
    b = 0;
    valid = 0;

    repeat (5) @(posedge clk);
    rst = 0;

    @(posedge clk);
    a = 4'd5;
    b = 4'd3;
    valid = 1;
    @(posedge clk);
    a = 4'd7;
    b = 4'd8;
    valid = 1;
    @(posedge clk);
    a = 4'd2;
    b = 4'd2;
    valid = 0;
    @(posedge clk);
    $finish;
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      sum <= 0;
    end else begin
      if (valid) begin
        sum <= a + b;
      end
    end
  end

  // Use BR_ASSERT_STATIC
  `BR_ASSERT_STATIC(width_check_a, Width == 4)

  // Use BR_ASSERT
  `BR_ASSERT(sum_range_check_a, sum <= 15)

  // Use BR_ASSUME
  // Not really useful (redundant with assert above) but it
  // should work like an assert when not being used in formal
  `BR_ASSUME(sum_range_check_m, sum <= 15)

  // Use BR_ASSERT_CR
  logic custom_clk;
  logic custom_rst;
  always #7 custom_clk = ~custom_clk;
  initial begin
    custom_clk = 0;
    custom_rst = 1;
    #15 custom_rst = 0;
  end
  `BR_ASSERT_CR(valid_data_check_a, (valid == 1) |-> (sum == a + b), custom_clk, custom_rst)
  // Not really useful (redundant with assert above) but it
  // should work like an assert when not being used in formal
  `BR_ASSUME_CR(valid_data_check_m, (valid == 1) |-> (sum == a + b), custom_clk, custom_rst)

  // Use BR_ASSERT_COMB
  `BR_ASSERT_COMB(inputs_nonzero_a, (a != 0) || (b != 0))

  // Use BR_COVER
  `BR_COVER(sum_overflow_a, sum > 15)

  // Use BR_COVER_CR
  `BR_COVER_CR(valid_transition_a, (valid == 1), custom_clk, custom_rst)

  // Use BR_COVER_COMB
  `BR_COVER_COMB(inputs_equal_a, (a == b))

endmodule : br_asserts_test
