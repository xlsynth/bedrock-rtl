// Copyright 2024-2025 The Bedrock-RTL Authors
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

module br_asserts_test;

  logic clk;
  logic rst;

  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic [4:0] sum_next;
  logic valid;

  localparam int Width = 4;

  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst = 1;
    a = 1;
    b = 1;
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

  assign sum_next = a + b;

  always_ff @(posedge clk) begin
    if (rst) begin
      sum <= 0;
    end else begin
      if (valid) begin
        sum <= sum_next;
      end
    end
  end

  // Use BR_ASSERT_STATIC
  `BR_ASSERT_STATIC(width_check_a, Width == 4)

  // Use BR_ASSERT_FINAL
  `BR_ASSERT_FINAL(valid_0_final_a, valid == 0)

  // Use BR_ASSERT_INCL_RST
  `BR_ASSERT_INCL_RST(valid_0_during_rst_a, rst |-> valid == 0)
  `BR_ASSERT_INCL_RST_C(valid_0_during_rst_c_a, rst |-> valid == 0, clk)

  // Use BR_ASSERT
  `BR_ASSERT(sum_range_check_a, sum <= 15)
  `BR_ASSERT_FPV(sum_range_check_fpv_a, sum <= 15)

  // Use BR_ASSERT_KNOWN variants
  `BR_ASSERT_KNOWN(valid_known_a, valid)
  `BR_ASSERT_KNOWN_VALID(sum_known_when_valid_a, valid, sum)
  `BR_ASSERT_KNOWN_CR(valid_known_cr_a, valid, clk, rst)
  `BR_ASSERT_KNOWN_VALID_CR(sum_known_when_valid_cr_a, valid, sum, clk, rst)

  // Use BR_ASSUME
  // Not really useful (redundant with assert above) but it
  // should work like an assert when not being used in formal
  `BR_ASSUME(sum_range_check_m, sum <= 15)
  `BR_ASSUME_FPV(sum_range_check_fpv_m, sum <= 15)

  // Use BR_ASSERT_CR
  logic custom_clk;
  logic custom_rst;
  assign custom_clk = clk;
  assign custom_rst = rst;
  `BR_ASSERT_CR(valid_data_check_a, (valid == 1) |-> (sum_next == a + b), custom_clk, custom_rst)
  `BR_ASSERT_CR_FPV(valid_data_check_fpv_a, (valid == 1) |-> (sum_next == a + b), custom_clk,
                    custom_rst)
  // Not really useful (redundant with assert above) but it
  // should work like an assert when not being used in formal
  `BR_ASSUME_CR(valid_data_check_m, (valid == 1) |-> (sum_next == a + b), custom_clk, custom_rst)
  `BR_ASSUME_CR_FPV(valid_data_check_fpv_m, (valid == 1) |-> (sum_next == a + b), custom_clk,
                    custom_rst)

  always_comb begin
    `BR_ASSERT_IMM(inputs_nonzero_in_comb_a, (a != 0) || (b != 0))
  end

  initial begin
    `BR_ASSERT_IMM(imm_assert_initial_a, 1 === 1)
    `BR_COVER_IMM(imm_cover_initial_c, 0 === 0)
  end

  final begin
    `BR_ASSERT_IMM(imm_assert_final_a, 1 === 1)
    `BR_COVER_IMM(imm_cover_final_c, 0 === 0)
  end

  // Use BR_ASSERT_COMB
  `BR_ASSERT_COMB(inputs_nonzero_a, (a != 0) || (b != 0))
  `BR_ASSERT_COMB_FPV(inputs_nonzero_fpv_a, (a != 0) || (b != 0))

  // Use BR_COVER
  `BR_COVER(sum_overflow_a, sum > 15)
  `BR_COVER_FPV(sum_overflow_fpv_a, sum > 15)

  // Use BR_COVER_CR
  `BR_COVER_CR(valid_transition_a, (valid == 1), custom_clk, custom_rst)
  `BR_COVER_CR_FPV(valid_transition_fpv_a, (valid == 1), custom_clk, custom_rst)

  // Use BR_COVER_COMB
  `BR_COVER_COMB(inputs_equal_a, (a == b))
  `BR_COVER_COMB_FPV(inputs_equal_fpv_a, (a == b))

  final begin
    // Unfortunately this will get printed even if an assertion fails :(
    // No way to query the number of failing assertions from within the test.
    $display("TEST PASSED");
    $finish;
  end

endmodule : br_asserts_test
