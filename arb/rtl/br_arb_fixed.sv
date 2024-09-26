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

// Bedrock-RTL Fixed-Priority Arbiter
//
// Grants a single request at a time with fixed (strict) priority
// where the lowest index requester has the highest priority.
//
// An enable signal controls whether any grant can be made.

`include "br_asserts_internal.svh"

module br_arb_fixed #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,  // Only used for assertions
    input logic rst,  // Only used for assertions
    input logic enable,
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] grant
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumRequesters-1:0] grant_internal;

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder (
      .in (request),
      .out(grant_internal)
  );

  assign grant = {NumRequesters{enable}} & grant_internal;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_ASSERT_IMPL(grant_only_when_enabled_A, |grant |-> enable)

endmodule : br_arb_fixed
