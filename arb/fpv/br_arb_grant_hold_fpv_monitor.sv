// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Arbiter Grant Holder

`include "br_asserts.svh"
`include "br_fv.svh"

module br_arb_grant_hold_fpv_monitor #(
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    // If a requester has grant_hold == 1 and is granted, the grant will be held until
    // grant_hold for that requester is deasserted.
    input logic [NumRequesters-1:0] grant_hold,
    // If 1 and grant_hold is 0, then the arbiter's priority will update whenever it makes a grant.
    input logic enable_grant_hold_update,
    // Connections to the arbiter.
    input logic [NumRequesters-1:0] grant_from_arb,
    input logic enable_priority_update_to_arb,
    // The final grant signal post-hold.
    input logic [NumRequesters-1:0] grant
);

  // only when grant_hold[i] and grant[i] are both 1, the grant will be held
  logic fv_hold;
  assign fv_hold = |(grant_hold & grant) && enable_grant_hold_update;

  // ----------FV assumptions----------
  `BR_ASSUME(grant_onehot_a, $onehot0(grant_from_arb))

  // ----------FV assertions----------
  `BR_ASSERT(grant_stable_if_hold_a, fv_hold |=> $stable(grant))
  `BR_ASSERT(enable_priority_hold_a, fv_hold |=> enable_priority_update_to_arb == 1'b0)

endmodule : br_arb_grant_hold_fpv_monitor

bind br_arb_grant_hold br_arb_grant_hold_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
