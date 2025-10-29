// SPDX-License-Identifier: Apache-2.0


// Unit test for br_asserts_internal.svh macros

`timescale 1ns / 1ps

`include "br_asserts_internal.svh"

module br_asserts_internal_test;

  logic clk;
  logic rst;

  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic valid;

  localparam int Width = 4;

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

  // Use BR_ASSERT_INTG
  `BR_ASSERT_INTG(sum_range_check_intg, sum <= 15)

  // Use BR_ASSERT_KNOWN_INTG
  `BR_ASSERT_KNOWN_INTG(valid_known_intg, valid)

  // Use BR_ASSERT_KNOWN_VALID_INTG
  `BR_ASSERT_KNOWN_VALID_INTG(sum_known_when_valid_intg, valid, sum)

  // Use BR_ASSERT_KNOWN_CR_INTG
  `BR_ASSERT_KNOWN_CR_INTG(valid_known_cr_intg, valid, clk, rst)

  // Use BR_ASSERT_KNOWN_VALID_CR_INTG
  `BR_ASSERT_KNOWN_VALID_CR_INTG(sum_known_when_valid_cr_intg, valid, sum, clk, rst)

  // Use BR_ASSERT_INCL_RST_INTG
  `BR_ASSERT_INCL_RST_INTG(a_zero_in_reset_intg, a == 0)

  // Use BR_ASSERT_INCL_RST_C_INTG
  `BR_ASSERT_INCL_RST_C_INTG(b_zero_in_reset_intg, b == 0, clk)

  // Use BR_ASSERT_IMPL
  `BR_ASSERT_IMPL(sum_correct_impl, (valid == 1) |-> (sum == a + b))

  // Use BR_ASSERT_KNOWN_IMPL
  `BR_ASSERT_KNOWN_IMPL(valid_known_impl, valid)

  // Use BR_ASSERT_KNOWN_VALID_IMPL
  `BR_ASSERT_KNOWN_VALID_IMPL(sum_known_when_valid_impl, valid, sum)

  // Use BR_ASSERT_KNOWN_CR_IMPL
  `BR_ASSERT_KNOWN_CR_IMPL(valid_known_cr_impl, valid, clk, rst)

  // Use BR_ASSERT_KNOWN_VALID_CR_IMPL
  `BR_ASSERT_KNOWN_VALID_CR_IMPL(sum_known_when_valid_cr_impl, valid, sum, clk, rst)

  // Use BR_ASSERT_INCL_RST_IMPL
  `BR_ASSERT_INCL_RST_IMPL(a_zero_in_reset_impl, a == 0)

  // Use BR_ASSERT_INCL_RST_C_IMPL
  `BR_ASSERT_INCL_RST_C_IMPL(b_zero_in_reset_impl, b == 0, clk)

  // Use BR_ASSERT_CR_INTG
  logic custom_clk;
  logic custom_rst;
  always #7 custom_clk = ~custom_clk;
  initial begin
    custom_clk = 0;
    custom_rst = 1;
    #15 custom_rst = 0;
  end
  `BR_ASSERT_CR_INTG(valid_data_check_intg, (valid == 1) |-> (sum == a + b), custom_clk, custom_rst)

  // Use BR_ASSERT_CR_IMPL
  `BR_ASSERT_CR_IMPL(sum_nonzero_impl, (sum != 0), custom_clk, custom_rst)

  // Use BR_ASSERT_COMB_INTG
  `BR_ASSERT_COMB_INTG(inputs_nonzero_intg, (a != 0) || (b != 0))

  // Use BR_ASSERT_COMB_IMPL
  `BR_ASSERT_COMB_IMPL(sum_in_range_impl, sum <= 15)

  always_comb begin
    `BR_ASSERT_IMM_INTG(comb_sanity_imm_intg_a, 0 === 0)
    `BR_ASSERT_IMM_IMPL(comb_sanity_imm_impl_a, 0 === 0)
    `BR_COVER_IMM_INTG(comb_sanity_imm_intg_c, 0 === 0)
    `BR_COVER_IMM_IMPL(comb_sanity_imm_impl_c, 0 === 0)
  end

  initial begin
    `BR_ASSERT_IMM_INTG(initial_sanity_imm_intg_a, 0 === 0)
    `BR_ASSERT_IMM_IMPL(initial_sanity_imm_impl_a, 0 === 0)
    `BR_COVER_IMM_INTG(initial_sanity_imm_intg_c, 0 === 0)
    `BR_COVER_IMM_IMPL(initial_sanity_imm_impl_c, 0 === 0)
  end

  final begin
    `BR_ASSERT_IMM_INTG(final_sanity_imm_intg_a, 0 === 0)
    `BR_ASSERT_IMM_IMPL(final_sanity_imm_impl_a, 0 === 0)
    `BR_COVER_IMM_INTG(final_sanity_imm_intg_c, 0 === 0)
    `BR_COVER_IMM_IMPL(final_sanity_imm_impl_c, 0 === 0)
  end

  // Use BR_COVER_INTG
  `BR_COVER_INTG(sum_overflow_intg, sum > 15)

  // Use BR_COVER_IMPL
  `BR_COVER_IMPL(sum_zero_impl, sum == 0)

  // Use BR_COVER_CR_INTG
  `BR_COVER_CR_INTG(valid_transition_intg, (valid == 1), custom_clk, custom_rst)

  // Use BR_COVER_CR_IMPL
  `BR_COVER_CR_IMPL(sum_max_impl, sum == 15, custom_clk, custom_rst)

  // Use BR_COVER_COMB_INTG
  `BR_COVER_COMB_INTG(inputs_equal_intg, (a == b))

  // Use BR_COVER_COMB_IMPL
  `BR_COVER_COMB_IMPL(inputs_opposite_impl, (a == ~b))

endmodule : br_asserts_internal_test
