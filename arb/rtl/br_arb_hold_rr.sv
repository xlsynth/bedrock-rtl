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

// Bedrock-RTL Round-Robin Arbiter with Grant Hold
//
// Grants a single request at a time using round-robin priority. Requester 0
// initializes as the highest priority. On the cycle after a grant, the granted
// index becomes the lowest priority and the next higher index (modulo NumRequesters)
// becomes the highest priority.
//
// On average, round-robin arbitration is fair to all requesters so long as
// each requester does not withdraw its request until it is granted.
//
// The enable_priority_update signal allows the priority state to update when a
// grant is made. If low, grants can still be made, but the priority will remain
// unchanged for the next cycle.
//
// The grant_hold signal will cause the arbiter to disable further arbitration
// once the specified requester is granted, and maintain the grant to that
// requester until the grant_hold signal for that requester is deasserted. The
// grant combinationally depends on grant_hold. If grant_hold is asserted for a
// requester that is not granted, it has no effect on that grant.
//
// There is zero latency from request to grant.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_arb_hold_rr #(
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] grant,
    input logic [NumRequesters-1:0] grant_hold
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------

  `BR_COVER_INTG(grant_hold_multihot_c, !$onehot0(grant_hold))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic enable_priority_update_int;
  logic [NumRequesters-1:0] grant_pre;

  br_arb_rr #(
      .NumRequesters(NumRequesters)
  ) br_arb_rr_inst (
      .clk,
      .rst,
      .enable_priority_update(enable_priority_update_int),
      .request,
      .grant(grant_pre)
  );

  br_arb_hold_internal #(
      .NumRequesters(NumRequesters)
  ) br_arb_hold_internal_inst (
      .clk,
      .rst,
      .grant_hold,
      .enable_priority_update_pre_hold(enable_priority_update),
      .grant_pre_hold(grant_pre),
      .enable_priority_update_post_hold(enable_priority_update_int),
      .grant_post_hold(grant)
  );

endmodule : br_arb_hold_rr
