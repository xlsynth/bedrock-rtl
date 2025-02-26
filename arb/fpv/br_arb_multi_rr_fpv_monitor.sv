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

// Bedrock-RTL Round-Robin Arbiter with multiple grants per cycle FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_multi_rr_fpv_monitor #(
    // Number of requesters. Must be at least 2.
    parameter int NumRequesters = 2,
    // Maximum number of grants per cycle. Must be at least 2 and at most NumRequesters.
    parameter int MaxGrantPerCycle = NumRequesters,
    localparam int GrantCountWidth = $clog2(MaxGrantPerCycle + 1)
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant,
    // A different view of grant with a single bit set in each vector.
    // The grants are given in order from highest priority to lowest.
    input logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] grant_ordered,
    // The number of requests that can be granted on a given cycle.
    input logic [GrantCountWidth-1:0] grant_allowed,
    // The number of requests being granted on the current cycle.
    input logic [GrantCountWidth-1:0] grant_count
);

  // ----------FV Modeling Code----------
  // pick 2 random index among NumRequesters
  logic [$clog2(NumRequesters)-1:0] i, j;
  `BR_FV_2RAND_IDX(i, j, NumRequesters)
  // pick 2 random index among MaxGrantPerCycle
  logic [$clog2(MaxGrantPerCycle)-1:0] x, y;
  `BR_FV_2RAND_IDX(x, y, MaxGrantPerCycle)
  `BR_ASSUME(x_smaller_than_y_a, x < y)

  logic [NumRequesters-1:0][$clog2(NumRequesters)-1:0] cur_pri, nxt_pri;
  logic [$clog2(NumRequesters)-1:0] pivot;
  logic [$clog2(NumRequesters)-1:0] idx;
  logic [$clog2(NumRequesters)-1:0] low_pri_idx, high_pri_idx;

  // Requester 0 initializes as the highest priority
  // cur_pri is initialized to be [0,1,2...,NumRequesters-1]
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      for (int i = 0; i < NumRequesters; i++) begin
        cur_pri[i] <= NumRequesters - 1 - i;
      end
    end else if (enable_priority_update && |grant) begin
      cur_pri <= nxt_pri;
    end
  end

  // Compute nxt_pri based on the current cycle's grant.
  // The rule is: among all granted requesters, find the one with the lowest cur_pri.
  // Let that index be the pivot. Then update nxt_pri as follows:
  //   nxt_pri[pivot] = 0;
  //   nxt_pri[(pivot+1)%NumRequesters] = NumRequesters - 1;
  //   nxt_pri[(pivot+2)%NumRequesters] = NumRequesters - 2;
  //   ... and so on.
  always_comb begin
    nxt_pri = cur_pri;
    pivot   = 0;
    for (int i = 0; i < NumRequesters; i++) begin
      if (grant[i]) begin
        if (!grant[pivot] || (cur_pri[i] < cur_pri[pivot])) begin
          pivot = i;
        end
      end
    end
    // Update nxt_pri in a cyclic fashion starting at pivot.
    // k = 0 assigns pivot's position; then subsequent positions get descending priorities.
    for (int k = 0; k < NumRequesters; k++) begin
      idx = (pivot + k) % NumRequesters;
      if (k == 0) nxt_pri[idx] = 0;
      else nxt_pri[idx] = NumRequesters - k;
    end
  end

  // The grants are given in order from highest priority to lowest.
  // if x < y, grant_ordered[x] has higher priority than grant_ordered[y]
  `BR_FV_IDX(high_pri_idx, grant_ordered[x], NumRequesters)
  `BR_FV_IDX(low_pri_idx, grant_ordered[y], NumRequesters)

  // ----------FV assumptions----------
  // req_hold_until_grant_a is ONLY enabled in standard use case where request won't drop without its grant
  // If request drop without its grant, these checks FAIL
  //      grant_ordered_priority_a
  //      round_robin_a
  //      no_deadlock_a
  for (genvar n = 0; n < NumRequesters; n++) begin : gen_asm
    `BR_ASSUME(req_hold_until_grant_a, request[n] && !grant[n] |=> request[n])
  end
  `BR_ASSUME(grant_allowed_range_a, grant_allowed <= MaxGrantPerCycle)

  // ----------Sanity Check----------
  `BR_ASSERT(no_spurious_grant_a, grant[i] |-> request[i])
  `BR_ASSERT(grant_allowed_check_a, $countones(grant) <= grant_allowed)
  `BR_ASSERT(grant_count_check_a, $countones(grant) == grant_count)
  for (genvar m = 0; m < MaxGrantPerCycle; m++) begin : gen_ast
    `BR_ASSERT(grant_ordered_onehot_a, $onehot0(grant_ordered[m]))
    for (genvar n = 0; n < NumRequesters; n++) begin : gen_gnt
      `BR_ASSERT(grant_ordered_sanity_a, grant_ordered[m][n] |-> grant[n])
    end
  end
  `BR_ASSERT(
      grant_ordered_priority_a,
      |grant_ordered[x] && |grant_ordered[y] |-> cur_pri[high_pri_idx] > cur_pri[low_pri_idx])

  // ----------Fairness Check----------
  // verilog_lint: waive-start line-length
  `BR_ASSERT(
      round_robin_a,
      request[i] |-> not (!grant[i] && enable_priority_update && (grant_allowed != 'd0) throughout grant[j] [-> 2]))
  // verilog_lint: waive-stop line-length

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |request && |grant_allowed |-> |grant)
  `BR_ASSERT(
      no_deadlock_a,
      request[i] |-> s_eventually grant[i] || !enable_priority_update || (grant_allowed == 'd0))

  // ----------Critical Covers----------
  `BR_COVER(all_request_c, &request)

endmodule : br_arb_multi_rr_fpv_monitor

bind br_arb_multi_rr br_arb_multi_rr_fpv_monitor #(
    .NumRequesters(NumRequesters),
    .MaxGrantPerCycle(MaxGrantPerCycle)
) monitor (.*);
