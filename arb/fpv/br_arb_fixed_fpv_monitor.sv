// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fixed-Priority Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_arb_fixed_fpv_monitor #(
    // Must be at least 1
    parameter int NumRequesters = 1
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
  localparam int IdxWidth = br_math::clamped_clog2(NumRequesters);
  logic [IdxWidth-1:0] i, j;

  if (NumRequesters > 1) begin : gen_multi_requester_idxs
    `BR_FV_2RAND_IDX(i, j, NumRequesters)
  end else begin : gen_single_requester_idx
    assign i = 1'b0;
    assign j = 1'b0;
  end

  `BR_ASSERT(strict_priority_a, (i < j) && request[i] && request[j] |-> !grant[j])

endmodule : br_arb_fixed_fpv_monitor

bind br_arb_fixed br_arb_fixed_fpv_monitor #(.NumRequesters(NumRequesters)) monitor (.*);
