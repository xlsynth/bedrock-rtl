// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_arb_fixed #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input logic clk,  // Only used for assertions
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ INPUT_NOT_READ
    input logic rst,  // Only used for assertions
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] grant
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_COVER_INTG(request_multihot_c, !$onehot0(request))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_arb_fixed_internal #(
      .NumRequesters(NumRequesters)
  ) br_arb_fixed_internal (
      .request,
      .can_grant(),  // Unused internal signal
      .grant
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_a, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)

endmodule : br_arb_fixed
