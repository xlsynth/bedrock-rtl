// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_weighted_rr_fpv_monitor #(
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
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][WeightWidth-1:0] request_weight,
    input logic [NumRequesters-1:0] grant
);

  localparam int Latency = (MaxAccumulatedWeight + 1) * (NumRequesters - 1);

  // ----------FV Modeling Code----------
  logic [$clog2(NumRequesters)-1:0] i, j;
  logic [NumRequesters-1:0][AccumulatedWeightWidth-1:0] fv_weight_cnt, fv_weight_cnt_next;

  // pick two random indices
  `BR_FV_2RAND_IDX(i, j, NumRequesters)

  for (genvar n = 0; n < NumRequesters; n++) begin : gen_fv
    always_comb begin
      fv_weight_cnt_next[n] = (request[n] && enable_priority_update && (fv_weight_cnt[n] == 'd0)) ?
                              request_weight[n] - (grant[n] & enable_priority_update) :
                              fv_weight_cnt[n] - (grant[n] & enable_priority_update);
    end
  end

  `BR_REG(fv_weight_cnt, fv_weight_cnt_next)

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumRequesters; n++) begin : gen_asm
    // request_weight has to be legal all the time, even if request is not high
    `BR_ASSUME(req_weight_range_a, request_weight[n] <= MaxWeight)
    // if request_weight = 0, request can stuck in arb
    `BR_ASSUME(req_weight_non_zero_a, request_weight[n] != 'd0)
    // req_hold_until_grant_a is ONLY enabled in standard use case:
    // request won't drop without all of its grant
    // If request drop without its grant, forward_progress_a FAILs
    `BR_ASSUME(
        req_hold_until_grant_a,
        request[n] && (fv_weight_cnt_next[n] != 'd0) |=> request[n] && $stable(request_weight[n]))
  end

  // ----------Sanity Check----------
  `BR_ASSERT(onehot_grant_a, $onehot0(grant))
  `BR_ASSERT(no_spurious_grant_a, grant[i] |-> request[i])

  // ----------Fairness Check----------
  // verilog_lint: waive-start line-length
  `BR_ASSERT(
      weighted_rr_a,
      (fv_weight_cnt[i] == 'd0) && (fv_weight_cnt_next[i] == 'd0) && enable_priority_update |-> !grant[i] || (request_weight[i] == 'd1))
  // verilog_lint: waive-stop line-length

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |request |-> |grant)
  // a requestor may need to wait up to a total of
  // (MaxAccumulatedWeight+1)*(NumRequesters-1) grants before being granted itself.
  `BR_ASSERT(forward_progress_a, request[i] |-> ##[0:Latency] grant[i] || !enable_priority_update)

  // ----------Critical Covers----------
  `BR_COVER(all_request_c, &request)
  `BR_COVER(request_max_weight_c, request[i] && (request_weight[i] == MaxWeight))


endmodule : br_arb_weighted_rr_fpv_monitor

bind br_arb_weighted_rr br_arb_weighted_rr_fpv_monitor #(
    .NumRequesters(NumRequesters),
    .MaxWeight(MaxWeight),
    .MaxAccumulatedWeight(MaxAccumulatedWeight)
) monitor (.*);
