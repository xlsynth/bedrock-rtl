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

// Bedrock-RTL Round-Robin Arbiter
//
// Grants a single request at a time using round-robin priority. Requester 0
// initializes as the highest priority. On the cycle after a grant, the granted
// index becomes the lowest priority and the next higher index (modulo NumRequesters)
// becomes the highest priority.
//
// On average, round-robin arbitration is fair to all requesters so long as each requester
// does not withdraw its request until it is granted.
//
// The update_priority signal causes the priority state to update and should
// only be true if there is a grant.
//
// There is zero latency from request to grant.

// This internal module exposes a 'can_grant' that is high if there are no
// requests of higher priority.  The final grant signal is equivalent to
// 'can_grant & request'.

`include "br_asserts.svh"

module br_arb_rr_internal #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  `BR_ASSERT_STATIC(num_requesters_gte_2_A, NumRequesters >= 2)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // We use two priority encoders to handle the modulo indexing.
  // * The first encoder uses a masked request vector to find the highest priority
  // request (if any exists) before wrapping around. These are the requests in the
  // range [RR_ptr, NumRequesters), where RR_ptr is the current round-robin priority
  // pointer.
  // * The second encoder uses the unmasked request vector to find the highest
  // priority request after the wraparound index. These are the requests in the
  // range [0, RR_ptr).
  //
  // The round-robin state is tracked in the rr_state_internal module. The
  // priority_mask output contains a mask of all request indices that are less
  // than the current  round-robin priority---those in the range [0, RR_ptr) that
  // are passed to the second (lower priority) encoder. The RR_ptr is initialized
  // to 0.

  logic update_priority;
  logic [NumRequesters-1:0] priority_mask;

  assign update_priority = enable_priority_update && |request;

  br_rr_state_internal #(
      .NumRequesters(NumRequesters)
  ) rr_state_internal (
      .clk,
      .rst,
      .update_priority,
      .grant,
      .last_grant(),
      .priority_mask
  );

  logic [NumRequesters-1:0] request_high;
  // request_high[0] is constant 0
  // ri lint_check_waive CONST_ASSIGN
  assign request_high = request & ~priority_mask;

  // If priority_mask[i] is 0, can_grant[i] looks at request_high[i-1:0]
  // If priority_mask[i] is 1, can_grant[i] looks at
  // request_high[NumRequesters-1:i+1] and request[i-1:0].
  // This avoids having can_grant[i] depend on request[i].
  // To make this a little easier to reason about,
  // we create the NxN matrix, request_priority, where
  // request_priority[i][j] means that request[j] is set and
  // of higher priority than request[i].
  // The diagonal, request_priority[i][i], is always 0.
  // Then can_grant[i] is equivalent to !(|request_priority[i]).
  logic [NumRequesters-1:0][NumRequesters-1:0] request_priority;

  // For i = 0, priority_mask[i] is never 0,
  assign request_priority[0] = {request_high[NumRequesters-1:1], 1'b0};
  assign request_priority[NumRequesters-1] =
      priority_mask[NumRequesters-1] ? {1'b0, request[NumRequesters-2:0]}
                                     : {1'b0, request_high[NumRequesters-2:0]};

  for (genvar i = 1; i < (NumRequesters - 1); i++) begin : gen_request_priority
    // The diagonal is always 0
    assign request_priority[i][i] = 1'b0;
    // For j < i, request[j] |-> request_priority[i][j] iff both are masked or both are unmasked
    assign request_priority[i][i-1:0] = priority_mask[i] ? request[i-1:0] : request_high[i-1:0];
    // For j > i, request[j] |-> request_priority[i][j] iff i is masked but j is not
    assign request_priority[i][NumRequesters-1:i+1] =
        priority_mask[i] ? request_high[NumRequesters-1:i+1] : '0;
  end

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_can_grant
    assign can_grant[i] = !(|request_priority[i]);
  end

  assign grant = request & can_grant;

endmodule : br_arb_rr_internal
