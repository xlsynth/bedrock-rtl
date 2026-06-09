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
`include "br_registers.svh"
`include "br_unused.svh"

module br_arb_weighted_lru #(
    // Must be at least 1
    parameter int NumRequesters = 1,
    // Must be at least 1
    parameter int MaxWeight = 1,
    // Maximum accumulated weight per requester. Must be at least MaxWeight.
    parameter int MaxAccumulatedWeight = MaxWeight,
    localparam int WeightWidth = $clog2(MaxWeight + 1),
    localparam int AccumulatedWeightWidth = $clog2(MaxAccumulatedWeight + 1)
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
    logic any_high_priority_request;
    logic [NumRequesters-1:0] can_grant;
    logic [NumRequesters-1:0][NumRequesters-1:0] state;
    logic [NumRequesters-1:0][NumRequesters-1:0] state_reg;
    logic [NumRequesters-1:0][NumRequesters-1:0] state_reg_next;

    logic incr_accumulated_weight;
    logic [NumRequesters-1:0] decr_accumulated_weight;
    logic [NumRequesters-1:0][AccumulatedWeightWidth-1:0] accumulated_weight;

    assign any_high_priority_request = |(request & request_priority);

    // This LRU state matrix implementation is copied from br_arb_lru_internal.
    // Implement the state matrix. We only need to maintain the upper triangular state (exclusive of
    // diagonal) in registers because the lower triangle is its complement. The diagonal is undefined
    // and unused (because we never need to compare the priority of a requester with itself).
    // There are NumRequesters * (NumRequesters - 1) / 2 flip-flops of priority state.
    for (genvar i = 0; i < NumRequesters; i++) begin : gen_state_row
      for (genvar j = 0; j < NumRequesters; j++) begin : gen_state_col
        // Upper triangle
        if (i < j) begin : gen_upper_tri
          // All bits in upper triangle init to 1'b1 (lowest numbered req wins)
          assign state_reg_next[i][j] = grant[i] ? 1'b0 : grant[j] ? 1'b1 : state[i][j];
          `BR_REGLI(state_reg[i][j], state_reg_next[i][j], enable_priority_update && |request, 1'b1)
          assign state[i][j] = state_reg[i][j];

          // Lower triangle is the inverse of upper triangle
        end else if (i > j) begin : gen_lower_tri
          assign state[i][j] = !state_reg[j][i];

          // Tie-off unused signals
          assign state_reg_next[i][j] = 1'b0;  // ri lint_check_waive CONST_ASSIGN
          assign state_reg[i][j] = 1'b0;  // ri lint_check_waive CONST_ASSIGN
          `BR_UNUSED_NAMED(states, {state_reg_next[i][j], state_reg[i][j]})

          // The diagonal is unused. Tie off signals.
        end else begin : gen_diag
          // ri lint_check_waive CONST_ASSIGN
          assign {state_reg_next[i][j], state_reg[i][j], state[i][j]} = '0;
          `BR_UNUSED_NAMED(states, {state_reg_next[i][j], state_reg[i][j], state[i][j]})
        end
      end
    end

    // Fold weighted priority into the LRU matrix. Since request_priority is
    // registered state, request only passes through one pairwise comparison.
    always_comb begin
      for (int i = 0; i < NumRequesters; i++) begin
        can_grant[i] = 1'b1;
        for (int j = 0; j < NumRequesters; j++) begin
          if (i != j) begin
            can_grant[i] &=
                !request[j] ||
                ((request_priority[i] == request_priority[j]) ? state[i][j] : request_priority[i]);
          end
        end
      end
    end

    assign grant = request & can_grant;

    // Track per-request accumulated weight.
    assign incr_accumulated_weight =
        enable_priority_update && |request && !any_high_priority_request;
    assign decr_accumulated_weight = enable_priority_update ? grant : '0;

    for (genvar i = 0; i < NumRequesters; i++) begin : gen_accumulated_weight
      br_counter #(
          .MaxValue(MaxAccumulatedWeight),
          .MaxChange(MaxWeight),
          .MaxDecrement(1),
          .EnableSaturate(1),
          .EnableWrap(0),
          .EnableCoverZeroChange(0),
          .EnableCoverReinit(0),
          .EnableAssertFinalInitialValue(0)
      ) br_counter (
          .clk,
          .rst,
          .reinit(1'b0),
          .initial_value({AccumulatedWeightWidth{1'b0}}),
          .incr_valid(incr_accumulated_weight),
          .incr(request_weight[i]),
          .decr_valid(decr_accumulated_weight[i]),
          .decr(WeightWidth'(1'b1)),
          .value(accumulated_weight[i]),
          .value_next()
      );

      assign request_priority[i] = |accumulated_weight[i];
    end

    `BR_ASSERT_IMPL(disable_priority_update_A,
                    !enable_priority_update |=> $stable({accumulated_weight, state}))
    `BR_ASSERT_IMPL(high_priority_grant_A,
                    any_high_priority_request |-> |(grant & request_priority))
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
