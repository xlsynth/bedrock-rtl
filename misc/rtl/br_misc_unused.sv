// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Unused Signal Sink
//
// Sinks an unused signal and waives the corresponding lint errors internally.
// It is expected that this logic will be automatically removed by the synthesis
// tool.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the `BR_UNUSED(signal) or `BR_UNUSED_NAMED(name, expression)
// convenience macros defined in macros/br_unused.svh.

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
