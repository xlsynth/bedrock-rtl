// Copyright 2025 The Bedrock-RTL Authors
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

`include "br_asserts.svh"
`include "br_registers.svh"

module ext_arb_fv_monitor #(
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=2.
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
      // TODO: still under discussion
      // sanity check:
      // assumption arb_grant_eventually_a can only be added
      // if assertion arb_req_hold_until_grant_a is true
      `BR_ASSERT(arb_req_hold_until_grant_a,
                 arb_request[r][f] && !arb_grant[r][f] |=> arb_request[r][f])
      `BR_ASSUME(arb_grant_eventually_a, arb_request[r][f] |-> s_eventually arb_grant[r][f])
    end
  end

endmodule
