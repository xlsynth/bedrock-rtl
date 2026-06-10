// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Weighted Least-Recently-Used Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_weighted_lru_fpv_monitor #(
    parameter int NumRequesters = 1,
    parameter int MaxWeight = 1,
    parameter int MaxAccumulatedWeight = MaxWeight,
    localparam int WeightWidth = $clog2(MaxWeight + 1),
    localparam int AccumulatedWeightWidth = $clog2(MaxAccumulatedWeight + 1)
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
    input logic [NumRequesters-1:0] grant
);

  localparam int Latency = (MaxAccumulatedWeight + 1) * (NumRequesters - 1);
  localparam int ModelWeightWidth = AccumulatedWeightWidth + 1;

  // ----------FV Modeling Code----------
  logic [$clog2(NumRequesters)-1:0] i;
  `BR_ASSUME(index_stable_a, $stable(i) && (i < NumRequesters))

  logic [NumRequesters-1:0][AccumulatedWeightWidth-1:0] fv_weight_cnt, fv_weight_cnt_next;
  logic [NumRequesters-1:0][ModelWeightWidth-1:0] fv_weight_cnt_plus_weight;
  logic [NumRequesters-1:0] fv_request_priority;
  logic any_high_priority_request;
  logic [NumRequesters-1:0] lru_request;

  // Weighted priority selects the active requesters with nonzero accumulated weight.
  // If none exist, all active requesters are LRU-eligible after the refill step.
  // Feed this filtered request set into the basic LRU checker so it verifies the tie-break
  // among only the requesters that the weighted policy is allowed to grant.
  assign any_high_priority_request = |(request & fv_request_priority);
  assign lru_request = any_high_priority_request ? request & fv_request_priority : request;

  for (genvar n = 0; n < NumRequesters; n++) begin : gen_fv
    assign fv_request_priority[n] = |fv_weight_cnt[n];

    // Model the RTL accumulator update: when no active requester has accumulated weight,
    // refill all requesters with saturating weights, then consume one grant credit.
    always_comb begin
      fv_weight_cnt_plus_weight[n] =
          ModelWeightWidth'(fv_weight_cnt[n]) + ModelWeightWidth'(request_weight[n]);

      fv_weight_cnt_next[n] = fv_weight_cnt[n];
      if (enable_priority_update && |request) begin
        if (!any_high_priority_request) begin
          fv_weight_cnt_next[n] =
              (fv_weight_cnt_plus_weight[n] > ModelWeightWidth'(MaxAccumulatedWeight)) ?
              AccumulatedWeightWidth'(MaxAccumulatedWeight) :
              AccumulatedWeightWidth'(fv_weight_cnt_plus_weight[n]);
        end

        if (grant[n] && (fv_weight_cnt_next[n] != 'd0)) begin
          fv_weight_cnt_next[n] = fv_weight_cnt_next[n] - 'd1;
        end
      end
    end
  end

  `BR_REG(fv_weight_cnt, fv_weight_cnt_next)

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumRequesters; n++) begin : gen_asm
    `BR_ASSUME(req_weight_range_a, request_weight[n] <= MaxWeight)
    `BR_ASSUME(req_weight_non_zero_a, request_weight[n] != 'd0)
    if (NumRequesters > 1) begin : gen_multi_req
      `BR_ASSUME(req_hold_until_grant_a,
                 request[n] && (!grant[n] || (fv_weight_cnt_next[n] != 'd0)) |=> request[n] &&
              $stable(
                     request_weight[n]
                 ))
    end
  end

  // ----------Sanity Check----------
  `BR_ASSERT(onehot_grant_a, $onehot0(grant))
  `BR_ASSERT(no_spurious_grant_a, grant[i] |-> request[i])
  `BR_ASSERT(must_grant_a, |request |-> |grant)

  // ----------Weighted Priority Check----------
  `BR_ASSERT(grant_is_eligible_a, grant[i] |-> lru_request[i])

  // ----------LRU Tie-Break Check----------
  lru_basic_fpv_monitor #(
      .NumRequesters(NumRequesters)
  ) lru_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request(lru_request),
      .grant
  );

  // ----------Forward Progress Check----------
  `BR_ASSERT(forward_progress_a, request[i] |-> ##[0:Latency] grant[i] || !enable_priority_update)

  // ----------Critical Covers----------
  `BR_COVER(all_request_c, &request)
  `BR_COVER(request_max_weight_c, request[i] && (request_weight[i] == MaxWeight))
  if (NumRequesters != 1) begin : gen_multi_req_covers
    `BR_COVER(lru_request_multihot_c, !$onehot0(lru_request))
  end

endmodule : br_arb_weighted_lru_fpv_monitor

bind br_arb_weighted_lru br_arb_weighted_lru_fpv_monitor #(
    .NumRequesters(NumRequesters),
    .MaxWeight(MaxWeight),
    .MaxAccumulatedWeight(MaxAccumulatedWeight)
) monitor (.*);
