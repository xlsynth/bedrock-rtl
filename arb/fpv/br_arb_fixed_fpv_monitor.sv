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

// Bedrock-RTL Fixed-Priority Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_arb_fixed_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  // ----------arb checks----------
  arb_basic_fpv_monitor #(
      .NumRequesters(NumRequesters)
  ) arb_check (
      .clk,
      .rst,
      .enable_priority_update(1'b1),
      .request,
      .grant
  );

  // ----------Fixed-Priority Check----------
  logic [$clog2(NumRequesters)-1:0] i, j;
  `BR_FV_2RAND_IDX(i, j, NumRequesters)

  `BR_ASSERT(strict_priority_a, (i < j) && request[i] && request[j] |-> !grant[j])

endmodule : br_arb_fixed_fpv_monitor

bind br_arb_fixed br_arb_fixed_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
