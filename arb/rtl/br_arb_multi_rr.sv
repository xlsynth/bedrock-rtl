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

// Bedrock-RTL Round-Robin Arbiter with multiple grants per cycle
//
// Grants a configurable number of requests at a time using round-robin
// priority. Requester 0 initializes as the highest priority. On the cycle after
// a grant, the granted index becomes the lowest priority and the next higher
// index (modulo NumRequesters) becomes the highest priority.
//
// On average, round-robin arbitration is fair to all requesters so long as each requester
// does not withdraw its request until it is granted.
//
// The enable_priority_update signal allows the priority state to update when a grant is made.
// If low, grants can still be made, but the priority will remain unchanged for the next cycle.
//
// The grant_allowed input specifies the number of requests to grant on each cycle.
//
// There is zero latency from request to grant.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_arb_multi_rr #(
    // Number of requesters. Must be at least 2.
    parameter int NumRequesters = 2,
    // Maximum number of grants per cycle. Must be at least 2 and at most NumRequesters.
    parameter int MaxGrantPerCycle = NumRequesters,
    // If 1, cover that that enable_priority_update can be low
    // Otherwise, assert that it is always high.
    parameter bit EnableCoverBlockPriorityUpdate = 1,
    localparam int GrantCountWidth = $clog2(MaxGrantPerCycle + 1)
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] grant,
    // A different view of grant with a single bit set in each vector.
    // The grants are given in order from highest priority to lowest.
    output logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] grant_ordered,
    // The number of requests that can be granted on a given cycle.
    input logic [GrantCountWidth-1:0] grant_allowed,
    // The number of requests being granted on the current cycle.
    output logic [GrantCountWidth-1:0] grant_count
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_requesters_a, NumRequesters >= 2)
  `BR_ASSERT_STATIC(legal_max_grant_per_cycle_a,
                    MaxGrantPerCycle >= 2 && MaxGrantPerCycle <= NumRequesters)

  `BR_ASSERT_INTG(grant_allowed_in_range_a, grant_allowed <= MaxGrantPerCycle)
  `BR_COVER_INTG(more_request_than_allowed_a, $countones(request) > grant_allowed)

  if (EnableCoverBlockPriorityUpdate) begin : gen_block_priority_update_cover
    `BR_COVER_INTG(block_priority_update_a, !enable_priority_update && |request)
  end else begin : gen_priority_update_always_enabled_assert
    `BR_ASSERT_INTG(priority_update_always_enabled_a, |request |-> enable_priority_update)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  localparam int RequestCountWidth = $clog2(NumRequesters + 1);
  localparam int GrantSelectWidth = $clog2(MaxGrantPerCycle);

  logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] all_grants;
  logic [MaxGrantPerCycle-1:0] grant_valid;
  logic [NumRequesters-1:0] lowest_prio, lowest_prio_next, lowest_prio_init;
  logic [RequestCountWidth-1:0] request_count;
  logic [GrantCountWidth-1:0] last_grant_select_ext;
  logic [GrantSelectWidth-1:0] last_grant_select;
  logic priority_update;
  logic less_request_than_allowed;

  // binary to unary decoding of grant_allowed to grant_valid
  // This should satisfy $countones(grant_valid) == grant_allowed
  // with the ones filling in from LSB.
  // i.e. if MaxGrantPerCycle = 3, then
  // grant_allowed = 2'd0 -> grant_valid = 3'b000
  // grant_allowed = 2'd1 -> grant_valid = 3'b001
  // grant_allowed = 2'd2 -> grant_valid = 3'b011
  // grant_allowed = 2'd3 -> grant_valid = 3'b111
  for (genvar i = 0; i < MaxGrantPerCycle; i++) begin : gen_grant_valid
    assign grant_valid[i] = grant_allowed > i;
  end

  // Generate all the possible grants.
  br_enc_priority_dynamic #(
      .NumRequesters(NumRequesters),
      .NumResults(MaxGrantPerCycle)
  ) u_enc_priority_dynamic (
      .clk,
      .rst,
      .in (request),
      .lowest_prio,
      .out(all_grants)
  );

  // Updating the priority state. The next lowest priority should be the last
  // request to be granted. Count how many were granted, then take 1 minus
  // that and select from all_grants.

  br_enc_countones #(
      .Width(NumRequesters)
  ) br_enc_countones_inst (
      .in(request),
      .count(request_count)
  );

  assign less_request_than_allowed = request_count <= RequestCountWidth'(grant_allowed);
  assign grant_count = less_request_than_allowed ? GrantCountWidth'(request_count) : grant_allowed;
  assign last_grant_select_ext = grant_count - 1'b1;
  assign last_grant_select = GrantSelectWidth'(last_grant_select_ext);

  br_mux_bin #(
      .NumSymbolsIn(MaxGrantPerCycle),
      .SymbolWidth (NumRequesters)
  ) br_mux_bin_last_grant (
      .select(last_grant_select),
      .in(all_grants),
      .out_valid(),
      .out(lowest_prio_next)
  );

  assign priority_update  = enable_priority_update && (|request) && (grant_allowed > '0);
  assign lowest_prio_init = {1'b1, {(NumRequesters - 1) {1'b0}}};

  `BR_REGLI(lowest_prio, lowest_prio_next, priority_update, lowest_prio_init)

  for (genvar i = 0; i < MaxGrantPerCycle; i++) begin : gen_grant_ordered
    assign grant_ordered[i] = grant_valid[i] ? all_grants[i] : '0;
  end

  // Combine the results of the priority encoder.
  always_comb begin
    grant = '0;
    for (int i = 0; i < MaxGrantPerCycle; i++) begin
      grant |= grant_ordered[i];
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(at_most_grant_allowed_granted_a, $countones(request & grant) <= grant_allowed)
  `BR_ASSERT_IMPL(grant_count_correct_a, $countones(grant) == grant_count)

  for (genvar i = 0; i < MaxGrantPerCycle; i++) begin : gen_grant_ordered_check
    `BR_ASSERT_IMPL(grant_ordered_onehot_a, $onehot0(grant_ordered[i]))
    `BR_ASSERT_IMPL(grant_ordered_subset_of_grant_a, (grant_ordered[i] & grant) == grant_ordered[i])
  end

  if (EnableCoverBlockPriorityUpdate) begin : gen_no_update_same_grants_assert
    `BR_ASSERT_IMPL(no_update_same_grants_A,
                    ##1 !$past(
                        enable_priority_update
                    ) && $stable(
                        request
                    ) && $stable(
                        grant_allowed
                    ) |-> $stable(
                        grant
                    ))
  end

endmodule
