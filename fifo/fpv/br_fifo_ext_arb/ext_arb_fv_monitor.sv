// SPDX-License-Identifier: Apache-2.0


`include "br_asserts.svh"
`include "br_registers.svh"

module ext_arb_fv_monitor #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2
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
    // we will use br_arb, all of them can guarantee same cycle grant
    `BR_ASSUME(same_cyc_arb_grant_a, |arb_request[r] |-> |arb_grant[r])
    for (genvar f = 0; f < NumFifos; f++) begin : gen_arb_request
      `BR_ASSUME(arb_legal_grant_a, arb_grant[r][f] |-> arb_request[r][f])
      // sanity check:
      // assumption arb_grant_eventually_a can only be added
      // if assertion arb_req_hold_until_grant_a is true
      `BR_ASSERT(arb_req_hold_until_grant_a,
                 arb_request[r][f] && !arb_grant[r][f] |=> arb_request[r][f])
      `BR_ASSUME(arb_grant_eventually_a, arb_request[r][f] |-> s_eventually arb_grant[r][f])
    end

    `BR_COVER(arb_request_multihot_a, !$onehot0(arb_request[r]))
  end

endmodule
