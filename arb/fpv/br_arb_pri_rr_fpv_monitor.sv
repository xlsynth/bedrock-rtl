// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Prioritized Round Robin Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_arb_pri_rr_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 2
    parameter int NumPriorities = 2
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][$clog2(NumPriorities)-1:0] request_priority,
    input logic [NumRequesters-1:0] grant
);
  `BR_ASSERT(must_grant_a, request != 0 |-> grant != 0)
  `BR_ASSERT(onehot_grant_a, $countones(grant) <= 1)
  `BR_COVER(all_request_c, request == '1)

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_req_0
    `BR_ASSUME(req_priority_range_a, request[i] |-> request_priority[i] < NumPriorities)
  end

  logic [$clog2(NumPriorities)-1:0] max_priority;
  always_comb begin
    max_priority = '0;
    for (int i = 0; i < NumRequesters; i++) begin
      if (request[i] && (request_priority[i] > max_priority)) begin
        max_priority = request_priority[i];
      end
    end
  end

  logic [NumRequesters-1:0] highest_priority_request;
  always_comb begin
    for (int i = 0; i < NumRequesters; i++) begin
      highest_priority_request[i] = request[i] && (request_priority[i] == max_priority);
    end
  end

  logic [NumRequesters-1:0] expected_grant;
  br_arb_rr #(
    .NumRequesters(NumRequesters)
  ) br_arb_rr_inst (
    .clk,
    .rst,
    .enable_priority_update,
    .request(highest_priority_request),
    .grant(expected_grant)
  );
  `BR_ASSERT(grant_match_a, grant == expected_grant)

endmodule : br_arb_pri_rr_fpv_monitor

bind br_arb_pri_rr br_arb_pri_rr_fpv_monitor#(.NumRequesters(NumRequesters), .NumPriorities(NumPriorities)) monitor (.*);
