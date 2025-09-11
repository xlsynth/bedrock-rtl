// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

// ri lint_check_waive EMPTY_MOD NO_OUTPUT
module br_misc_unused #(
    parameter int Width = 1  // Must be at least 1
) (
    input logic [Width-1:0] in
);

  `BR_ASSERT_STATIC(width_gte_1, Width >= 1)

  logic unused;  // ri lint_check_waive NOT_READ
  // cadence keep_signal_name unused
  assign unused = |in;

endmodule : br_misc_unused
