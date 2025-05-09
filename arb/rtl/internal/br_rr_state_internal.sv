`include "br_asserts_internal.svh"
`include "br_registers.svh"

// Copyright 2024-2025,2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Round-Robin State
//
// Tracks round-robin priority pointer state. When a grant is issued and
// update_priority is high, the last_grant register is updated to the
// grant index.
//
// The priority_mask output contains a mask of all request indices that
// are less than the current round-robin priority---those in the range
// [0, RR_ptr).

`include "br_asserts.svh"

module br_rr_state_internal #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic update_priority,
    input logic [NumRequesters-1:0] grant,
    output logic [NumRequesters-1:0] last_grant,
    output logic [NumRequesters-1:0] priority_mask
);

  `BR_ASSERT_STATIC(num_requesters_gte_2_A, NumRequesters >= 2)

  logic [NumRequesters-1:0] last_grant_init;

  // priority_mask selects all bits at or below the last grant.
  // e.g. if last grant is 001, then priority_mask is 001
  //      if last grant is 010, then priority_mask is 011
  //      if last grant is 100, then priority_mask is 111
  // priority_mask[0] is thus always 1.
  for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority_mask
    // For i = NumRequesters - 1, the full range will be selected
    // ri lint_check_waive FULL_RANGE
    assign priority_mask[i] = |last_grant[NumRequesters-1:i];
  end

  // ri lint_check_waive CONST_ASSIGN
  assign last_grant_init[NumRequesters-1]   = 1'b1;
  // ri lint_check_waive CONST_ASSIGN
  assign last_grant_init[NumRequesters-2:0] = '0;

  `BR_REGLI(last_grant, grant, update_priority, last_grant_init)

  `BR_ASSERT_IMPL(grant_onehot_A, update_priority |-> $onehot(grant))
  `BR_ASSERT_IMPL(last_grant_onehot_A, $onehot(last_grant))
  // For i > 0, priority_mask[i] |-> priority_mask[i-1]
  `BR_ASSERT_IMPL(priority_mask_thermometer_encoded_A, &(~(priority_mask >> 1) | priority_mask))

endmodule : br_rr_state_internal
