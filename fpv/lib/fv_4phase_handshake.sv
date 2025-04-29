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
