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

// Bedrock-RTL Weighted Round-Robin Arbiter with Grant Hold
//
// In steady state, grants are issued in proportion to the weights of
// the active requestors. For example, if requestors 1, 4, and 7 are
// asserted continuously, we'd expect requestor 1 to get w1/(w1+w4+w7)
// of the grants, where
//   w1 = request_weight[1]
//   w4 = request_weight[4]
//   w7 = request_weight[7]
//
// Inside the arbiter, each requestor has a "weight accumulator". This
// accumulator is unsigned and initialized to zero. The larger the
// MaxAccumulatedWeight, the more "memory" the arbiter has. Larger
// MaxAccumulatedWeight values allow a request to be deasserted and
// then reasserted for longer without losing its share of the arbiter
// output. A larger MaxAccumulatedWeight also tends to increase the
// burstiness of the arbiter output.
//
// The detailed operation of the arbiter is:
// 1. Assign a 1-bit priority to each requestor
//    a. Priority = 1 if accumulated weight is non-zero else 0
// 2. Grant the active requestor with the largest priority, using RR to break ties
// 3. If the accumulated weight of the granted requestor is zero,
//    a. Increment all accumulated weights by the corresponding weight (including
//       the grantee)
//    b. Saturate the counts at the configurable maximum accumulated weight
// 4. Decrement the accumulated weight of the granted requestor by 1.
//
// Note: Step 4 will never underflow unless the granted request_weight is zero.
// In this case, the accumulated weight is saturated at zero (instead of being
// decremented to -1).
//
// With this implementation, any request that remains asserted and whose
// request_weight is non-zero will eventually be granted. A requestor whose
// weight accumulators is zero could first need to wait
// MaxAccumulatedWeight*(NumRequesters-1) grants before all weight
// accumulators are zero. Then, it could need to wait an additional
// NumRequesters-1 grants before it is guaranteed to be selected.
// So, a requestor may need to wait up to a total of
// (MaxAccumulatedWeight+1)*(NumRequesters-1) grants before being granted itself.
//
// The enable_priority_update signal allows the priority state to update
// when a grant is made. If low, grants can still be made, but the priority
// will remain unchanged for the next cycle.
//
// The grant_hold signal will cause the arbiter to disable further arbitration
// once the specified requester is granted, and maintain the grant to that
// requester until the grant_hold signal for that requester is deasserted. The
// grant depends on a 1 cycle delayed version of grant_hold. If grant_hold is
// asserted for a requester that is not granted, it has no effect on that grant.
//
// A common use case is to connect grant_hold to the !last signal in a
// multi-beat request. In this case, after the first beat is arbitrated for,
// the arbiter will not switch requesters until after the last beat where
// grant_hold is deasserted.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_arb_hold_weighted_rr #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 1
    parameter int MaxWeight = 1,
    // Maximum accumulated weight per requester. Must be at least MaxWeight.
    parameter int MaxAccumulatedWeight = MaxWeight,
    localparam int WeightWidth = $clog2(MaxWeight + 1)
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
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

  br_arb_weighted_rr #(
      .NumRequesters(NumRequesters),
      .MaxWeight(MaxWeight),
      .MaxAccumulatedWeight(MaxAccumulatedWeight)
  ) br_arb_weighted_rr_inst (
      .clk,
      .rst,
      .enable_priority_update(enable_priority_update_int),
      .request,
      .request_weight,
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

endmodule : br_arb_hold_weighted_rr
