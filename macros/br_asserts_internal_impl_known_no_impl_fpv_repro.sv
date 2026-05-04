// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for BR_ASSERT_KNOWN*_IMPL expanding when BR_ENABLE_IMPL_CHECKS is unset.

`include "br_asserts_internal.svh"

module br_asserts_internal_impl_known_no_impl_fpv_repro (
    input logic clk,
    input logic rst
);
  logic watched;

  `BR_ASSERT_KNOWN_IMPL(watched_known_impl_should_be_noop_a, watched.missing_field)

endmodule : br_asserts_internal_impl_known_no_impl_fpv_repro
