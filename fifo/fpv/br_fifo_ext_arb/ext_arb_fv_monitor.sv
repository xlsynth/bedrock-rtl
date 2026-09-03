// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module ext_arb_fv_monitor #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter bit ArbiterAlwaysGrants = 1,
    parameter bit EnableLiveness = 1,
    parameter bit EnableCovers = 1
) (
    input logic clk,
    input logic rst,

    // External arbiter interface
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    input logic [NumReadPorts-1:0] arb_enable_priority_update
);

  // External arbiter interface assumptions
  for (genvar r = 0; r < NumReadPorts; r++) begin : gen_arb
    `BR_ASSUME(arb_onehot_grant_a, $onehot0(arb_grant[r]))
    if (ArbiterAlwaysGrants) begin : gen_always_grants
      // br_arb implementations can guarantee a same-cycle grant.
      `BR_ASSUME(same_cyc_arb_grant_a, |arb_request[r] |-> |arb_grant[r])
    end
    for (genvar f = 0; f < NumFifos; f++) begin : gen_arb_request
      `BR_ASSUME(arb_legal_grant_a, arb_grant[r][f] |-> arb_request[r][f])
      if (EnableLiveness) begin : gen_liveness
        // The eventual-grant assumption requires requests to remain asserted.
        `BR_ASSERT(arb_req_hold_until_grant_a,
                   arb_request[r][f] && !arb_grant[r][f] |=> arb_request[r][f])
        `BR_ASSUME(arb_grant_eventually_a, arb_request[r][f] |-> s_eventually arb_grant[r][f])
      end
    end

    if (EnableCovers) begin : gen_covers
      `BR_COVER(arb_request_multihot_a, !$onehot0(arb_request[r]))
    end
  end

endmodule
