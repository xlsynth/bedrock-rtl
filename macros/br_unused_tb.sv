// SPDX-License-Identifier: Apache-2.0

`include "br_unused.svh"

module br_unused_tb ();  // ri lint_check_waive NO_OUTPUT

  wire [1:0] foo = 2'b01;  // ri lint_check_waive CONST_ASSIGN
  wire bar = foo[0];  // ri lint_check_waive CONST_ASSIGN
  wire baz = 1'b0;
  wire qux = 1'b0;

  `BR_UNUSED(bar)
  `BR_UNUSED_NAMED(foo1, foo[1])
  `BR_UNUSED_TODO(bazqux, {baz, qux})

endmodule : br_unused_tb
