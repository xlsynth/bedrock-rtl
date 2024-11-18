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

// Bedrock-RTL LRU Arbiter FPV monitor

module br_arb_lru_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Only used for assertions
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Only used for assertions
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  `include "br_asserts.svh"

  logic [NumRequesters-1:0][$clog2(NumRequesters)-1:0] arb_priority;

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority
    always_ff @(posedge clk) begin
      if (rst) begin
        arb_priority[i] <= 0;
      end if (grant != 0) begin
        // The granted request will have priority reset to the lowest
        // All other requesters bump up their priority
        arb_priority[i] <= grant[i] ? 0 : arb_priority[i] + 1'b1;
      end
    end
  end

  `BR_ASSERT(must_grant_a, request != 0 |-> grant != 0)
  `BR_ASSERT(onehot_grant_a, $countones(grant) <= 1)
  `BR_COVER(all_request_c, request == '1)

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_req_0
    // Request must be hold until granted
    `BR_ASSUME(hold_request_until_grant_m, request[i] && !grant[i] |=> request[i])
    // Grant must be given to an active requester
    `BR_ASSERT(grant_active_req_a, grant[i] |-> request[i])
    // Grant must be returned to the requester after all other requesters are granted once
    `BR_ASSERT(grant_latency_a, request[i] && !grant[i] |-> ##[1:NumRequesters] grant[i])
    // High priority request must be grant the same cycle
    `BR_ASSERT(high_priority_grant_a, request[i] && (arb_priority[i] == NumRequesters - 1) |-> grant[i])
    for (genvar j = 0; j < NumRequesters; j++) begin : gen_req_1
      if (i != j) begin
        `BR_ASSERT(arb_priority_a, grant[j] |->
          !request[i] || (arb_priority[i] < arb_priority[j]) ||
          // TODO: when two requests have the same priority, the
          // lower index request should be granted first?
          (arb_priority[i] == arb_priority[j] && (i < j))
         )
       end
     end
   end

endmodule : br_arb_lru_fpv_monitor

bind br_arb_lru br_arb_lru_fpv_monitor#(.NumRequesters(NumRequesters)) monitor (.*);
