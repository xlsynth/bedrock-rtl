// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_arb_grant_hold #(
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    // If a requester has grant_hold == 1 and is granted, the grant will be held until
    // grant_hold for that requester is deasserted.
    input logic [NumRequesters-1:0] grant_hold,
    // If 1 and grant_hold is 0, then the arbiter's priority will update whenever it makes a grant.
    // If 0, then neither the arbiter's priority nor the grant hold state will update.
    input logic enable_grant_hold_update,
    // Connections to the arbiter.
    input logic [NumRequesters-1:0] grant_from_arb,
    output logic enable_priority_update_to_arb,
    // The final grant signal post-hold.
    output logic [NumRequesters-1:0] grant
);

  logic [NumRequesters-1:0] hold, hold_next;

  `BR_REGL(hold, hold_next, enable_grant_hold_update)
  assign enable_priority_update_to_arb = !(|hold) && enable_grant_hold_update;
  assign hold_next = grant & grant_hold;
  assign grant = |hold ? hold : grant_from_arb;
  `BR_ASSERT_IMPL(grants_actually_hold_a, |hold |-> $stable(grant))
  `BR_ASSERT_IMPL(enable_priority_update_mask_a, |hold |-> !enable_priority_update_to_arb)
  `BR_ASSERT_IMPL(enable_grant_hold_update_mask_a, !enable_grant_hold_update |=> $stable(hold))
endmodule : br_arb_grant_hold
