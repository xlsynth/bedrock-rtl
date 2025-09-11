// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"

module fv_4phase_handshake #(
    parameter bit Master = 1
) (
    input logic clk,
    input logic rst,
    input logic req,
    input logic ack
);

  if (Master) begin : gen_master
    `BR_ASSUME(req_rise_a, $rose(req) |-> !ack && !$fell(ack))
    `BR_ASSUME(req_fall_a, $fell(req) |-> ack)
    `BR_ASSUME(req_hold_until_ack_a, req && !ack |=> req)
    `BR_ASSERT(ack_rise_a, $rose(ack) |-> req && !$rose(req))
    `BR_ASSERT(ack_fall_a, $fell(ack) |-> !req)
    `BR_ASSERT(ack_hold_until_req_drop_a, ack && req |=> ack)
  end else begin : gen_slave
    `BR_ASSERT(req_rise_a, $rose(req) |-> !ack && !$fell(ack))
    `BR_ASSERT(req_fall_a, $fell(req) |-> ack)
    `BR_ASSERT(req_hold_until_ack_a, req && !ack |=> req)
    `BR_ASSUME(ack_rise_a, $rose(ack) |-> req && !$rose(req))
    `BR_ASSUME(ack_fall_a, $fell(ack) |-> !req)
    `BR_ASSUME(ack_hold_until_req_drop_a, ack && req |=> ack)
  end

endmodule : fv_4phase_handshake
