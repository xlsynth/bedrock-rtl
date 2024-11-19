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

// Bedrock-RTL Fixed-Priority Arbiter FPV monitor

`include "br_asserts.svh"

module br_arb_fixed_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

   `BR_ASSERT(must_grant_a, request != 0 |-> grant != 0)
   `BR_ASSERT(onehot_grant_a, $countones(grant) <= 1)
   `BR_COVER(all_request_c, request == '1)

   for (genvar i = 0; i < NumRequesters - 1; i++) begin : gen_high
     `BR_ASSERT(grant_active_req_a, grant[i] |-> request[i])
     for (genvar j = i + 1; j < NumRequesters; j++) begin : gen_low
       `BR_ASSERT(arb_priority_a, grant[j] |-> !request[i])
     end
   end

endmodule : br_arb_fixed_fpv_monitor

bind br_arb_fixed br_arb_fixed_fpv_monitor#(.NumRequesters(NumRequesters)) monitor (.*);
