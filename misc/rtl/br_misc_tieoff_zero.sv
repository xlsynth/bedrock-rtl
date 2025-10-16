// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Signal Tie-off-to-Zero Driver
//
// Drives a signal to constant 0s and waives the corresponding lint errors internally.
// It is expected that downstream logic will be automatically constant-propagated by
// the synthesis tool.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the convenience macros defined in macros/br_tieoff.svh.
//
// We have separate modules for tie-to-zero and tie-to-one because
// lint tools may complain about multiple parameters per line when wrapped up in a macro.

`include "br_asserts.svh"

module br_misc_tieoff_zero #(
    parameter int Width = 1  // Must be at least 1
) (
    output logic [Width-1:0] out
);

  `BR_ASSERT_STATIC(width_gte_1, Width >= 1)

  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  assign out = {Width{1'b0}};

endmodule : br_misc_tieoff_zero
