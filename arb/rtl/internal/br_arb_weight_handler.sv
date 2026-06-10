// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Arbiter Weight Handler
//
// Tracks a saturating weight accumulator for each requester and reports which
// accumulators are nonzero. When no active requester has accumulated weight,
// all accumulators are refilled from request_weight. The granted requester's
// accumulator is then decremented.

`include "br_asserts_internal.svh"

module br_arb_weight_handler #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 1
    parameter int MaxWeight = 1,
    // Maximum accumulated weight per requester. Must be at least MaxWeight.
    parameter int MaxAccumulatedWeight = MaxWeight,
    localparam int WeightWidth = $clog2(MaxWeight + 1),
    localparam int AccumulatedWeightWidth = $clog2(MaxAccumulatedWeight + 1)
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
    input logic [NumRequesters-1:0] grant,
    output logic [NumRequesters-1:0] request_priority
);

  `BR_ASSERT_STATIC(min_num_requesters_a, NumRequesters >= 2)
  `BR_ASSERT_STATIC(min_max_weight_a, MaxWeight >= 1)
  `BR_ASSERT_STATIC(max_accum_gte_max_weight_a, MaxAccumulatedWeight >= MaxWeight)

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_intg_checks
    `BR_ASSERT_INTG(request_weight_ne_0_a, request_weight[i] != 0)
  end

  logic any_high_priority_request;
  logic incr_accumulated_weight;
  logic [NumRequesters-1:0] decr_accumulated_weight;
  logic [NumRequesters-1:0][AccumulatedWeightWidth-1:0] accumulated_weight;

  assign any_high_priority_request = |(request & request_priority);
  assign incr_accumulated_weight = enable_priority_update && |request && !any_high_priority_request;
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

  `BR_ASSERT_IMPL(disable_priority_update_A, !enable_priority_update |=> $stable(accumulated_weight
                                                                                    ))

endmodule : br_arb_weight_handler
