// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Prioritized Round-Robin Arbiter
//
// Grants a single request at a time, by selecting the highest priority
// request using the per-request priority inputs. If there are multiple
// requests with the highest priority, then a round-robin arbiter is used
// to break ties. On the cycle after any grant, the granted index becomes
// the lowest round-robin priority and the next higher index (modulo
// NumRequesters) becomes the highest priority.
//
// The enable_priority_update signal allows the priority state to update
// when a grant is made. If low, grants can still be made, but the priority
// will remain unchanged for the next cycle.
//
// There is zero latency from request to grant.

`include "br_asserts_internal.svh"

module br_arb_pri_rr #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 2
    parameter int NumPriorities = 2
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][$clog2(NumPriorities)-1:0] request_priority,
    output logic [NumRequesters-1:0] grant
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------

  `BR_COVER_INTG(request_multihot_c, !$onehot0(request))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Track round-robin priority state
  logic update_priority;
  logic [NumRequesters-1:0] priority_mask;

  assign update_priority = enable_priority_update && |request;

  br_rr_state_internal #(
      .NumRequesters(NumRequesters)
  ) rr_state_internal (
      .clk,
      .rst,
      .update_priority,
      .grant,
      .last_grant(),
      .priority_mask
  );

  // Adopt the approach described in Towles et al.,
  // "Unifying on-chip and inter-node switching within the Anton 2 network"
  // where the priority and priority_mask are unrolled into a request
  // vector that is then fed into a fixed priority arbiter to find
  // the highest priority request. (Unlike the reference, the below
  // code assumes the LSB of the request vector is the highest priority
  // request.)

  // First unroll requests into NumPriorities+1 levels. The requests at
  // level 0 are the highest priority requests:
  //
  //   Level p=0: request priority = NP-1 and >= RR priority
  //
  // At Level 1, we combine the requests from level 0 that were disabled
  // by the RR priority AND those that are enabled with p=1:
  //
  //   Level p=1: (request priority = NP-2 and >= RR priority) OR
  //              (request priority = NP-1 and < RR priority)
  //
  // These two request sets are mutually exclusive and the NP-1 requests
  // appear before the NP-2 requests in the fixed priority order (LSB is
  // highest priority), so it is safe to OR them together.
  //
  // Generalizing, the requests at level p are:
  //
  //   Level p: (request priority = NP-1-p and >= RR priority) OR
  //             (request priority = NP-p and < RR priority)
  //
  // We use the thermometer encoded priority_mask to indicate if a
  // < RR priority. Also, thermometer encode the unrolled requests
  // vector (such that request_unrolled[p][i] implies
  // request_unrolled[p-1][i] for all p > 0) by replacing the
  // equality comparisons above with greater than or equal to:
  //
  //  Level p: (request priority >= NP-1-p and !priority_mask[i]) OR
  //             (request priority >= NP-p and priority_mask[i])
  //
  // Note: for a single priority level, the correspondes to the typical
  // approach used for a non-prioritized RR arbiter.

  logic [NumPriorities:0][NumRequesters-1:0] request_unrolled;

  assign request_unrolled[NumPriorities] = request;  // lowest priority

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_request_unrolled
    // p = 0 case (highest priority)
    assign request_unrolled[0][i] = request[i] &&
        (request_priority[i] == NumPriorities - 1) && !priority_mask[i];

    // p = 1 ... NumPriorities-2 cases
    for (genvar p = 1; p < NumPriorities - 1; p++) begin : gen_request_unrolled_pri
      assign request_unrolled[p][i] = request[i] && (
          ((request_priority[i] >= NumPriorities - 1 - p) && !priority_mask[i]) ||
          ((request_priority[i] >= NumPriorities - p) && priority_mask[i]));
    end

    // p = NumPriorities-1 case
    assign request_unrolled[NumPriorities-1][i] = request[i] && (
          !priority_mask[i] || ((request_priority[i] >= 1) && priority_mask[i]));
  end

  // Now, treat request_unrolled as a flattened vector and
  // create a mask to disable all lower priority requests using
  // a Kogge-Stone parallel prefix tree. Note: we only need
  // $clog2(NumRequesters-1) levels of prefix tree because
  // request_unrolled[i][j] -> request_unrolled[i-1][j] for
  // all i > 0 due the encoding used above.

  logic [$clog2(NumRequesters-1):0][NumPriorities:0][NumRequesters-1:0] any_higher_pri_req;

  assign any_higher_pri_req[0] = request_unrolled << 1;  // ri lint_check_waive TRUNC_LSHIFT
  for (genvar i = 0; i < $clog2(NumRequesters - 1); i++) begin : gen_any_higher_pri_req
    // ri lint_check_waive TRUNC_LSHIFT
    assign any_higher_pri_req[i+1] = any_higher_pri_req[i] | (any_higher_pri_req[i] << (1 << i));
  end

  // Finally, generate an unrolled grant by disabling unrolled
  // requests for which there are higher priority requests. Then
  // OR each unrolled grant into the final grant.

  logic [NumPriorities:0][NumRequesters-1:0] grant_unrolled;
  assign grant_unrolled = request_unrolled & ~any_higher_pri_req[$clog2(NumRequesters-1)];

  always_comb begin
    grant = '0;
    for (int i = 0; i <= NumPriorities; i++) begin
      grant |= grant_unrolled[i];
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_A, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_COVER_IMPL(grant_without_state_update_C, !enable_priority_update && |grant)

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority_range
    `BR_ASSERT_IMPL(requested_priority_range_A, request[i] |-> request_priority[i] < NumPriorities)
  end

endmodule : br_arb_pri_rr
