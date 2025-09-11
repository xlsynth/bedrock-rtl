// SPDX-License-Identifier: Apache-2.0

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_deskew #(
    parameter int Width = 1,  // Must be at least 1
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Positive edge-triggered clock.
    input  logic             clk,
    input  logic             in_valid_next,
    input  logic [Width-1:0] in,
    output logic             out_valid,
    output logic [Width-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_must_be_at_least_one_a, Width >= 1)

  // ri lint_check_waive ALWAYS_COMB
  `BR_COVER_COMB_INTG(in_valid_next_c, in_valid_next)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_next_a, !in_valid_next)
    `BR_ASSERT_FINAL(final_not_out_valid_a, !out_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  `BR_REGN(out_valid, in_valid_next)
  assign out = in;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(valid_delay_a, ##1 out_valid === $past(in_valid_next), clk, 1'b0)
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(data_delay_a, out === in)

endmodule : br_delay_deskew
