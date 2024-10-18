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

`include "br_asserts_internal.svh"

module br_arb_fixed #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Only used for assertions
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Only used for assertions
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
  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters)
  ) br_enc_priority_encoder (
      .clk,
      .rst,
      .in (request),
      .out(grant)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_a, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)

endmodule : br_arb_fixed
