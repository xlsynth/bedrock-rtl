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

// Bedrock-RTL Arbiter Grant Hold
//
// The grant_hold signal will cause the arbiter to disable further arbitration
// once the specified requester is granted, and maintain the grant to that
// requester until the grant_hold signal for that requester is deasserted. The
// grant depends on a 1 cycle delayed version of grant_hold. If grant_hold is
// asserted for a requester that is not granted, it has no effect on that grant.
//
// A common use case is to connect grant_hold to the !last signal in a
// multi-beat request. In this case, after the first beat is arbitrated for,
// the arbiter will not switch requesters until after the last beat where
// grant_hold is deasserted.
//
// If enable_priority_update_pre_hold is asserted, the internal registers will
// not be updated.

`include "br_registers.svh"

module br_arb_hold_internal #(
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    input logic [NumRequesters-1:0] grant_hold,
    input logic enable_priority_update_pre_hold,
    input logic [NumRequesters-1:0] grant_pre_hold,
    output logic enable_priority_update_post_hold,
    output logic [NumRequesters-1:0] grant_post_hold
);

  logic [NumRequesters-1:0] hold, hold_next;

  `BR_REGL(hold, hold_next, enable_priority_update_post_hold)
  assign enable_priority_update_post_hold = !(|hold) && enable_priority_update_pre_hold;
  assign hold_next = grant_post_hold & grant_hold;
  assign grant_post_hold = |hold ? hold : grant_pre_hold;

endmodule : br_arb_hold_internal
