// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Weighted Round-Robin Arbiter
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

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_arb_weighted_rr #(
    // Must be at least 1
    parameter int NumRequesters = 1,
    // Must be at least 1
    parameter int MaxWeight = 1,
    // Maximum accumulated weight per requester. Must be at least MaxWeight.
    parameter int MaxAccumulatedWeight = MaxWeight,
    localparam int WeightWidth = $clog2(MaxWeight + 1)
) (
    // ri lint_check_waive INPUT_NOT_READ
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
    output logic [NumRequesters-1:0] grant
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(min_num_requesters_a, NumRequesters >= 1)
  `BR_ASSERT_STATIC(min_max_weight_a, MaxWeight >= 1)
  `BR_ASSERT_STATIC(max_accum_gte_max_weight_a, MaxAccumulatedWeight >= MaxWeight)

  // We only care about request weight being non-zero when it's actually sampled
  // to update the accumulated weight. But this check is both stronger and simpler.
  for (genvar i = 0; i < NumRequesters; i++) begin : gen_intg_checks
    `BR_ASSERT_INTG(request_weight_ne_0_a, request_weight[i] != 0)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  if (NumRequesters == 1) begin : gen_1_req
    `BR_UNUSED(rst)
    `BR_UNUSED(enable_priority_update)
    `BR_UNUSED(request_weight)
    assign grant = request;

  end else begin : gen_any_higher_pri_req

    // Arbitrate, prioritizing requests with
    // non-zero accumulated weight
    logic [NumRequesters-1:0] request_priority;

    br_arb_pri_rr #(
        .NumRequesters(NumRequesters),
        .NumPriorities(2)
    ) br_arb_pri_rr_inst (
        .clk,
        .rst,
        .enable_priority_update,
        .request,
        .request_priority,
        .grant
    );

    br_arb_weight_handler #(
        .NumRequesters(NumRequesters),
        .MaxWeight(MaxWeight),
        .MaxAccumulatedWeight(MaxAccumulatedWeight)
    ) br_arb_weight_handler (
        .clk,
        .rst,
        .enable_priority_update,
        .request,
        .request_weight,
        .grant,
        .request_priority
    );
  end

  `BR_ASSERT_IMPL(no_update_same_grants_A, ##1 !$past(enable_priority_update) && $stable(request)
                                           |-> $stable(grant))
endmodule
