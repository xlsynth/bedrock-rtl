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
// An enable signal controls whether any grant can be made (and whether the corresponding
// priority update can occur).
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
    input logic enable,
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
  // If the masked request vector is not zero, then we use the grant from the first encoder; otherwise
  // we use the grant from the second encoder.
  //
  // The last_grant gets updated on the next cycle with the index of the grant, so that the
  // priority rotates in a round-robin fashion.
  // last_grant initializes to NumRequesters'b100....0 such that index 0 is the highest priority
  // out of reset.

  logic [NumRequesters-1:0] priority_mask;
  logic [NumRequesters-1:0] request_high;
  logic [NumRequesters-1:0] grant_high, grant_low;
  logic [$clog2(NumRequesters)-1:0] last_grant;

  always_comb begin
    priority_mask = '0;
    for (int i = 0; i < NumRequesters; i++) begin
      if (i > last_grant) begin
        priority_mask[i] = 1'b1;
      end
    end
  end

  assign request_high = request & priority_mask;

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder_high (
      .in (request_high),
      .out(grant_high)
  );

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder_low (
      .in (request),   // No need to mask since we only use grant_low if request_high is zero
      .out(grant_low)
  );

  // Mask the grant using the enable -- also ensures priority won't be updated if enable is low.
  assign grant = {NumRequesters{enable}} & (|request_high ? grant_high : grant_low);

  // We know that any request will always result in a grant if the arbiter is enabled,
  // so we can simplify the timing on the load enable.
  // Initialize the last_grant to 1000...0 to make index 0 the highest priority out of reset.
  `BR_REGIL(last_grant, grant, |request && enable, 1'b1 << (NumRequesters - 1))

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_ASSERT_IMPL(grant_only_when_enabled_A, |grant |-> enable)

  // TODO(mgottscho): Add more cases
  // TODO(mgottscho): Add covers on masked and unmasked cases

endmodule : br_arb_rr
