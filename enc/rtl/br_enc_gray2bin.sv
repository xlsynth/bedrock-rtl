// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_enc_gray2bin #(
    parameter int Width = 2  // Must be at least 2
) (
    input  logic [Width-1:0] gray,
    output logic [Width-1:0] bin
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_gte_2_a, Width >= 2)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  genvar i;

  assign bin[Width-1] = gray[Width-1];
  generate
    for (i = (Width - 2); i >= 0; i--) begin : gen_loop
      assign bin[i] = ^gray[Width-1:i];  // ri lint_check_waive FULL_RANGE
    end
  endgenerate

endmodule : br_enc_gray2bin
