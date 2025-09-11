// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_enc_bin2onehot #(
    parameter int NumValues = 2,  // Must be at least 1
    parameter int EnableInputRangeCheck = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // Width of the binary-encoded value. Must be at least $clog2(NumValues).
    parameter int BinWidth = br_math::clamped_clog2(NumValues)
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Used only for assertions
    input logic [BinWidth-1:0] in,
    input logic in_valid,
    output logic [NumValues-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_values_gte_2_a, NumValues >= 1)
  `BR_ASSERT_STATIC(binwidth_gte_log2_num_values_a, BinWidth >= br_math::clamped_clog2(NumValues))
  if (EnableInputRangeCheck) begin : gen_in_range_check
    `BR_ASSERT_INTG(in_within_range_a, in_valid |-> in < NumValues)
  end

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    for (int i = 0; i < NumValues; i++) begin
      out[i] = in_valid && (in == i);
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableInputRangeCheck) begin : gen_out_onehot
    `BR_ASSERT_IMPL(out_onehot_a, in_valid |-> $onehot(out))
  end
endmodule : br_enc_bin2onehot
