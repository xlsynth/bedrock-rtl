// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
    input logic enable_priority_update,
    // Connections to the arbiter.
    input logic [NumRequesters-1:0] grant_from_arb,
    input logic enable_priority_update_to_arb,
    // The final grant signal post-hold.
    input logic [NumRequesters-1:0] grant
);

  // ----------FV assumptions----------
  // pick a random index for assertion
  logic [$clog2(NumRequesters)-1:0] i;
  `BR_ASSUME(index_stable_a, $stable(i) && (i < NumRequesters))
  `BR_ASSUME(grant_onehot_a, $onehot0(grant_from_arb))

  // ----------FV assertions----------
  `BR_ASSERT(grant_stable_if_hold_a, ##1 grant_hold[i] && grant_from_arb[i] |=> $stable(grant))
  `BR_ASSERT(enable_priority_hold_a, |grant_hold |=> enable_priority_update_to_arb == 1'b0)
  `BR_ASSERT(enable_priority_a,
             ~|grant_hold |=> enable_priority_update_to_arb == enable_priority_update)

endmodule : br_arb_grant_hold_fpv_monitor

bind br_arb_grant_hold br_arb_grant_hold_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
