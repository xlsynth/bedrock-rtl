// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL LRU Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_lru_fpv_monitor #(
    // Must be at least 1
    parameter int NumRequesters = 1
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
  if (NumRequesters > 1) begin : gen_multi_req
    for (genvar i = 0; i < NumRequesters; i++) begin : gen_asm
      `BR_ASSUME(req_hold_until_grant_a, request[i] && !grant[i] |=> request[i])
    end
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
