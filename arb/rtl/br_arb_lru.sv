// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Least-Recently-Used (LRU) Arbiter
//
// Grants a single request at a time with a fair least-recently-used policy.
//
// The enable_priority_update signal allows the priority state to update when a grant is made.
// If low, grants can still be made, but the priority will remain unchanged for the next cycle.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_arb_lru #(
    // Must be at least 1
    parameter int NumRequesters = 1
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
  if (NumRequesters > 1) begin : gen_multi_req
    `BR_COVER_INTG(request_multihot_c, !$onehot0(request))
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_arb_lru_internal #(
      .NumRequesters(NumRequesters)
  ) br_arb_lru_internal (
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

endmodule : br_arb_lru
