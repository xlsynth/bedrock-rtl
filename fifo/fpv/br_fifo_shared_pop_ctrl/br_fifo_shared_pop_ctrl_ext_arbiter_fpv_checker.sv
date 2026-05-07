// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

module br_fifo_shared_pop_ctrl_ext_arbiter_fpv_checker #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter bit ArbiterAlwaysGrants = 1
) (
    input logic clk,
    input logic rst,

    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_can_grant,
    input logic [NumReadPorts-1:0] arb_enable_priority_update
);

  for (genvar r = 0; r < NumReadPorts; r++) begin : gen_read_port
    // The external arbiter selects at most one requester per read port.
    `BR_ASSUME(arb_can_grant_onehot_a, $onehot0(arb_request[r] & arb_can_grant[r]))

    // br_flow_mux_core uses can_grant for ready and grant for data select, so they must agree.
    `BR_ASSUME(arb_grant_matches_can_grant_a, arb_grant[r] == (arb_request[r] & arb_can_grant[r]))

    if (ArbiterAlwaysGrants) begin : gen_arbiter_always_grants
      // The selected arbiter policy must produce a same-cycle grant when any request is present.
      `BR_ASSUME(arb_always_grants_a, |arb_request[r] |-> |arb_grant[r])
    end

    // The read crossbar is permanently ready to issue RAM reads, so priority updates stay enabled.
    `BR_ASSERT(arb_enable_priority_update_a, arb_enable_priority_update[r])

    for (genvar f = 0; f < NumFifos; f++) begin : gen_fifo
      // The DUT must hold requests until the external arbiter grants them.
      `BR_ASSERT(arb_req_hold_until_grant_a,
                 arb_request[r][f] && !arb_grant[r][f] |=> arb_request[r][f])

      // Prevent an unfair external arbiter model from starving an outstanding request forever.
      `BR_ASSUME(arb_grant_eventually_a, arb_request[r][f] |-> s_eventually arb_grant[r][f])
    end

    `BR_COVER(arb_request_multihot_c, !$onehot0(arb_request[r]))
  end

endmodule : br_fifo_shared_pop_ctrl_ext_arbiter_fpv_checker
