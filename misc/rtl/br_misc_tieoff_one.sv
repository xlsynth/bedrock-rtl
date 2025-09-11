// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

module br_misc_tieoff_one #(
    parameter int Width = 1  // Must be at least 1
) (
    output logic [Width-1:0] out
);

  `BR_ASSERT_STATIC(width_gte_1, Width >= 1)

  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  assign out = {Width{1'b1}};

endmodule : br_misc_tieoff_one
