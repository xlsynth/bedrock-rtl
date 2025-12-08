// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Arbiter basic FV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module arb_basic_fpv_monitor #(
    parameter int NumRequesters = 1
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0] grant
);

  // ----------FV Modeling Code----------
  localparam int IdxWidth = br_math::clamped_clog2(NumRequesters);
  logic [IdxWidth-1:0] i, j;

  if (NumRequesters > 1) begin : gen_multi_requester_idxs
    `BR_FV_2RAND_IDX(i, j, NumRequesters)
  end else begin : gen_single_requester_idx
    assign i = 1'b0;
    assign j = 1'b0;
  end

  // ----------Sanity Check----------
  `BR_ASSERT(onehot_grant_a, $onehot0(grant))
  `BR_ASSERT(no_spurious_grant_a, grant[i] |-> request[i])

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |request |-> |grant)
  `BR_ASSERT(no_deadlock_a, request[i] |-> s_eventually grant[i] || !enable_priority_update)

  // ----------Critical Covers----------
  `BR_COVER(all_request_c, &request)

endmodule : arb_basic_fpv_monitor
