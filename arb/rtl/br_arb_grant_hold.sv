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
//
// This module is intended to be connected to an arbiter, and can be used to pause
// arbitration and hold the grant for a given requester.
//
// When deasserted, the grant_ready signal will cause the arbiter to disable further
// arbitration once the specified requester is granted, and maintain the grant to that
// requester until the grant_ready signal for that requester is deasserted. On the cycle
// following grant_ready asserted for the current grant, the arbitration is accepted
// via enable_priority_update, and a new grant is passed through. If grant_ready is
// deasserted for a requester that is not granted, it has no effect on that grant.
//
// A common use case is to connect grant_ready to the last signal in a
// multi-beat request. In this case, after the first beat is arbitrated for,
// the arbiter will not switch requesters until after the last beat where
// grant_ready is deasserted.
//
// If enable_priority_update is deasserted, the internal registers will
// not be updated.

`include "br_registers.svh"

module br_arb_grant_hold #(
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    // If a requester has grant_ready == 0 and is granted, the grant will be held until
    // grant_ready for that requester is asserted.
    input logic [NumRequesters-1:0] grant_ready,
    // Can be used with hierarchical arbiters. OK to tie to 1.
    input logic enable_priority_update,
    // Connections to the arbiter.
    input logic [NumRequesters-1:0] grant_from_arb,
    output logic enable_priority_update_to_arb,
    // The final grant signal post-hold.
    output logic [NumRequesters-1:0] grant
);

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  `BR_COVER_INTG(grant_hold_multihot_c, !$onehot0(grant_hold))
`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  logic [NumRequesters-1:0] hold, hold_next;

  `BR_REGL(hold, hold_next, enable_priority_update)
  assign enable_priority_update_to_arb = !(|hold) && enable_priority_update;
  assign hold_next = grant & ~grant_ready;
  assign grant = |hold ? hold : grant_from_arb;
`BR_ASSERT_IMPL(grants_actually_hold_a, any_hold_grant |=> grant == $past(grant))
endmodule : br_arb_grant_hold
