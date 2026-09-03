// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Weighted Least-Recently-Used (LRU) Arbiter
//
// In steady state, grants are issued in proportion to the weights of
// the active requesters. Least-recently-used priority breaks ties between
// requesters at the same weighted priority.
//
// Each requester has an unsigned weight accumulator initialized to zero.
// The detailed operation of the arbiter is:
// 1. Assign a 1-bit weighted priority to each requester
//    a. Priority = 1 if accumulated weight is non-zero else 0
// 2. Grant the least-recently-used active requester with the largest priority
// 3. If no active requester has non-zero accumulated weight,
//    a. Increment all accumulated weights by the corresponding weight
//    b. Saturate the counts at the configurable maximum accumulated weight
// 4. Decrement the accumulated weight of the granted requester by 1.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_arb_weighted_lru #(
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

  // We only care about request weight being non-zero when it is sampled
  // to update the accumulated weight. This check is stronger and simpler.
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

  end else begin : gen_n_req
    logic [NumRequesters-1:0] request_priority;
    logic [NumRequesters-1:0][NumRequesters-1:0] state;
    logic [NumRequesters-1:0][NumRequesters-1:0] priority_matrix;

    br_lru_state_internal #(
        .NumRequesters(NumRequesters)
    ) br_lru_state_internal (
        .clk,
        .rst,
        .update_priority(enable_priority_update && |request),
        .grant,
        .state
    );

    // Fold weighted priority into the LRU matrix. Since request_priority is
    // registered state, request does not pass through this comparison.
    for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority_matrix_row
      for (genvar j = 0; j < NumRequesters; j++) begin : gen_priority_matrix_col
        assign priority_matrix[i][j] =
            (request_priority[i] == request_priority[j]) ? state[i][j] : request_priority[i];
      end
    end

    br_arb_pairwise_core_internal #(
        .NumRequesters(NumRequesters)
    ) br_arb_pairwise_core_internal (
        .request,
        .priority_matrix,
        .can_grant(),
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

    `BR_ASSERT_IMPL(high_priority_grant_A,
                    |(request & request_priority) |-> |(grant & request_priority))
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(grant_onehot0_A, $onehot0(grant))
  `BR_ASSERT_IMPL(always_grant_A, |request |-> |grant)
  `BR_ASSERT_IMPL(grant_implies_request_A, (grant & request) == grant)
  `BR_ASSERT_IMPL(no_update_same_grants_A, ##1 !$past(enable_priority_update) && $stable(request)
                                           |-> $stable(grant))
  `BR_COVER_IMPL(grant_without_state_update_C, !enable_priority_update && |grant)

endmodule : br_arb_weighted_lru
