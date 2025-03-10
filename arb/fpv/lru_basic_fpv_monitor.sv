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

// Bedrock-RTL LRU Arbiter basic FV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module lru_basic_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  // ----------FV Modeling Code----------
  logic [$clog2(NumRequesters)-1:0] x, y;
  `BR_FV_2RAND_IDX(x, y, NumRequesters)

  logic [NumRequesters-1:0][$clog2(NumRequesters):0] arb_priority;
  logic [$clog2(NumRequesters):0] granted_priority;

  always_comb begin
    granted_priority = 0;
    for (int i = 0; i < NumRequesters; i++) begin
      if (grant[i]) begin
        granted_priority = arb_priority[i];
      end
    end
  end

  genvar i, j;
  // Implementation:
  // - At the beginning, all requester set to high priority = NumRequesters
  // - When a request is granted, the priority set to the lowest = 0
  //   All other requesters with the priority lower than the granted requester
  //   will bump its priority by 1.
  for (i = 0; i < NumRequesters; i++) begin : gen_priority
    always @(posedge clk) begin
      if (rst) begin
        arb_priority[i] <= NumRequesters;
      end else begin
        if (grant[i] && enable_priority_update) begin
          arb_priority[i] <= 0;
        end else if (enable_priority_update && (grant != 0) &&
                    (arb_priority[i] < granted_priority)) begin
          arb_priority[i] <= arb_priority[i] + $clog2(NumRequesters)'(1);
        end
      end
    end
  end

  logic [NumRequesters-1:0][$clog2(NumRequesters):0] wait_count;
  // count the number of cycles that the requester is not granted
  for (i = 0; i < NumRequesters; i++) begin : gen_counter
    always @(posedge clk) begin
      if (rst) begin
        wait_count[i] <= 0;
      end else begin
        if (grant[i]) begin
          wait_count[i] <= 0;
        end else if (enable_priority_update && (grant != 0) && request[i] && !grant[i]) begin
          wait_count[i] <= wait_count[i] + $clog2(NumRequesters)'(1);
        end
      end
      `BR_COVER(wait_count_c, wait_count[i] == NumRequesters - 1)
    end
  end

  // ----------Forward Progress Check----------
  // Grant must be returned to the requester after all other requesters are granted once
  `BR_ASSERT(grant_latency_a, request[x] && (wait_count[x] == NumRequesters - 1) |-> grant[x])

  // ----------Fairness Check----------
  // Check correct arbitration priority
  `BR_ASSERT(arb_priority_a, grant[y] |-> !request[x] || (arb_priority[x] < arb_priority[y]) ||
                             // When two requests have the same priority, the
                             // lower index request should be granted
                             (arb_priority[x] == arb_priority[y]) && (y < x))

  // ----------Critical Covers----------
  for (i = 0; i < NumRequesters; i++) begin : gen_req_0
    for (j = 0; j < NumRequesters; j++) begin : gen_req_1
      if (i != j) begin : gen_reqs
        // Cover all combinations of priorities
        `BR_COVER(same_priority_c, request[i] && request[j] && (arb_priority[i] == arb_priority[j]))
        `BR_COVER(low_priority_c, request[i] && request[j] && (arb_priority[i] < arb_priority[j]))
        `BR_COVER(high_priority_c, request[i] && request[j] && (arb_priority[i] > arb_priority[j]))
      end
    end
  end

endmodule : lru_basic_fpv_monitor
