// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_arb_rr #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
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

  br_arb_rr_internal #(
      .NumRequesters(NumRequesters)
  ) br_arb_rr_internal (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .can_grant(),  // Unused internal signal
      .grant
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_a, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_ASSERT_IMPL(no_update_same_grants_A, ##1 !$past(enable_priority_update) && $stable(request)
                                           |-> $stable(grant))
  `BR_COVER_IMPL(grant_without_state_update_c, !enable_priority_update && |grant)

  // TODO(mgottscho): Add more cases
  // TODO(mgottscho): Add covers on masked and unmasked cases

endmodule : br_arb_rr
