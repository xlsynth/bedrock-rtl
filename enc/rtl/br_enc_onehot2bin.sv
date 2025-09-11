// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_enc_onehot2bin #(
    parameter int NumValues = 2,  // Must be at least 1
    // Width of the binary-encoded value. Must be at least $clog2(NumValues).
    parameter int BinWidth = br_math::clamped_clog2(NumValues)
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 clk,        // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 rst,        // Used only for assertions
    input  logic [NumValues-1:0] in,
    output logic                 out_valid,
    output logic [ BinWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_values_gte_1_a, NumValues >= 1)
  `BR_ASSERT_STATIC(binwidth_gte_log2_num_values_a, BinWidth >= br_math::clamped_clog2(NumValues))
  // This is necessary to avoid an integer overflow in the for-loop below.
  `BR_ASSERT_STATIC(binwidth_lt_32_a, BinWidth < 32)
  `BR_ASSERT_INTG(in_onehot_a, $onehot0(in))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign out_valid = |in;
  if (NumValues == 1) begin : gen_single_value
    assign out = '0;
  end else begin : gen_multi_value
    always_comb begin
      out = '0;
      for (int i = 1; i < NumValues; i++) begin
        // If multiple bits are set, this is undefined behavior.
        if (in[i]) begin
          out |= BinWidth'($unsigned(i));
        end
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(out_within_range_a, out < NumValues)

endmodule : br_enc_onehot2bin
