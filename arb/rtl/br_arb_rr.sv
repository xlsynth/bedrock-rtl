// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Round-Robin Arbiter
//
// Grants a single request at a time using round-robin priority. Requester 0
// initializes as the highest priority. On the cycle after a grant, the granted
// index becomes the lowest priority and the next higher index (modulo NumRequesters)
// becomes the highest priority.
//
// On average, round-robin arbitration is fair to all requesters so long as each requester
// does not withdraw its request until it is granted.
//
// The enable_priority_update signal allows the priority state to update when a grant is made.
// If low, grants can still be made, but the priority will remain unchanged for the next cycle.
//
// There is zero latency from request to grant.

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
  // Rely on submodule integration checks

  // TODO(mgottscho): add checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // last_grant is the only state in the design. The requester with the last grant
  // is the lowest priority, so the next highest index (modulo NumRequesters) is the
  // highest priority.
  //
  // We use two priority encoders to handle the modulo indexing.
  // * The first encoder uses a masked request vector to find the highest priority request
  // (if any exists) before wrapping around.
  // * The second encoder uses the unmasked request vector to find the highest priority request
  // after the wraparound index.
  //
  // If the masked request vector is not zero, then we use the grant from the first encoder;
  // otherwise we use the grant from the second encoder.
  //
  // The last_grant gets updated on the next cycle with the index of the grant, so that the
  // priority rotates in a round-robin fashion.
  // last_grant initializes to NumRequesters'b100....0 such that index 0 is the highest priority
  // out of reset.

  logic [NumRequesters-1:0] priority_mask;
  logic [NumRequesters-1:0] request_high;
  logic [NumRequesters-1:0] grant_high;
  logic [NumRequesters-1:0] grant_low;
  logic [$clog2(NumRequesters)-1:0] last_grant;
  logic [$clog2(NumRequesters)-1:0] last_grant_next;

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority_mask
    // priority_mask[0] is constant 0
    // ri lint_check_waive CONST_ASSIGN
    assign priority_mask[i] = i > last_grant;
  end

  // request[0] is constant 0
  // ri lint_check_waive CONST_ASSIGN
  assign request_high = request & priority_mask;

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder_high (
      .clk,
      .rst,
      .in (request_high),
      .out(grant_high)
  );

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder_low (
      .clk,
      .rst,
      .in (request),   // No need to mask since we only use grant_low if request_high is zero
      .out(grant_low)
  );

  assign grant = |request_high ? grant_high : grant_low;

  // We know that any request will always result in a grant,
  // so we can simplify the timing on the load enable.
  // Initialize the last_grant the most significant requester
  // to make index 0 the highest priority out of reset.
  br_enc_onehot2bin #(
      .NumValues(NumRequesters)
  ) br_enc_onehot2bin (
      .clk,
      .rst,
      .in(grant),
      // unused because we know we only consume last_grant_next when
      // |request (which also implies |grant)
      .out_valid(),
      .out(last_grant_next)
  );

  `BR_REGIL(last_grant, last_grant_next, enable_priority_update && |request, NumRequesters - 1)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_a, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_COVER_IMPL(grant_without_state_update_c, !enable_priority_update && |grant)

  // TODO(mgottscho): Add more cases
  // TODO(mgottscho): Add covers on masked and unmasked cases

endmodule : br_arb_rr
