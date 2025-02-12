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

// Bedrock-RTL LRU Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_lru_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  // ----------FV assumptions----------
  // This assumption is ONLY enabled in standard use case where request won't drop without its grant
  // If request drop without its grant, these checks FAIL
  //      no_deadlock_a
  //      lru_a
  for (genvar i = 0; i < NumRequesters; i++) begin : gen_asm
    `BR_ASSUME(req_hold_until_grant_a, request[i] && !grant[i] |=> request[i])
  end

  // ----------arb checks----------
  arb_basic_fpv_monitor #(
      .NumRequesters(NumRequesters)
  ) arb_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .grant
  );

  // ----------LRU checks----------
  lru_basic_fpv_monitor #(
      .NumRequesters(NumRequesters)
  ) lru_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .grant
  );

endmodule : br_arb_lru_fpv_monitor

bind br_arb_lru br_arb_lru_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
