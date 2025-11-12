// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Line Skew (Valid to Valid-Next)
//
// Retimes a delay line using aligned valid/data to instead
// use valid-next/data (i.e., valid runs one cycle ahead of data).
// Adds 1 cycle of latency to the datapath to allow the valid to run ahead.
//
// This module has no reset.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_skew #(
    parameter int Width = 1,  // Must be at least 1
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Positive edge-triggered clock.
    input  logic             clk,
    input  logic             in_valid,
    input  logic [Width-1:0] in,
    output logic             out_valid_next,
    output logic [Width-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_must_be_at_least_one_a, Width >= 1)

  // ri lint_check_waive ALWAYS_COMB
  `BR_COVER_COMB_INTG(in_valid_c, in_valid)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
    `BR_ASSERT_FINAL(final_not_out_valid_next_a, !out_valid_next)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign out_valid_next = in_valid;
  `BR_REGLN(out, in, in_valid)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(valid_delay_a, out_valid_next === in_valid)
  `BR_ASSERT_CR_IMPL(data_delay_a, !$isunknown(in_valid) && in_valid |=> out === $past(in), clk,
                     1'b0)

endmodule : br_delay_skew
