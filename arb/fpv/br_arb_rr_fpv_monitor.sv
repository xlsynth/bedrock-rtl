// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Round Robin Priority Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_rr_fpv_monitor #(
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
  //      round_robin_a
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

  // ----------Round Robin checks----------
  rr_basic_fpv_monitor #(
      .NumRequesters(NumRequesters),
      .EnableAssumeRequestStability(1)
  ) rr_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request,
      .grant
  );

endmodule : br_arb_rr_fpv_monitor

bind br_arb_rr br_arb_rr_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
