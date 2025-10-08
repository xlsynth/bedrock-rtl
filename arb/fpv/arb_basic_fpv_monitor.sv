// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Arbiter basic FV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module arb_basic_fpv_monitor #(
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
  logic [$clog2(NumRequesters)-1:0] i, j;
  `BR_FV_2RAND_IDX(i, j, NumRequesters)

  // ----------Sanity Check----------
  `BR_ASSERT(onehot_grant_a, $onehot0(grant))
  `BR_ASSERT(no_spurious_grant_a, grant[i] |-> request[i])

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |request |-> |grant)
  `BR_ASSERT(no_deadlock_a, request[i] |-> s_eventually grant[i] || !enable_priority_update)

  // ----------Critical Covers----------
  `BR_COVER(all_request_c, &request)

endmodule : arb_basic_fpv_monitor
