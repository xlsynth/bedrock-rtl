// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fixed Priority Arbiter with multiple grants per cycle
//
// Grants a configurable number of requests at a time using fixed
// priority. Requester 0 has the highest priority.
//
// The grant_allowed input specifies the number of requests to grant on each cycle.
//
// There is zero latency from request to grant.

`include "br_asserts_internal.svh"

module br_arb_multi_fixed #(
    // Number of requesters. Must be at least 2.
    parameter int NumRequesters = 2,
    // Maximum number of grants per cycle. Must be at least 2 and at most NumRequesters.
    parameter int MaxGrantPerCycle = NumRequesters,
    // If 1, cover that the number of requests is greater than the number of allowed grants.
    // Otherwise, assert that there are never more requests than allowed grants.
    parameter bit EnableCoverMoreRequestThanAllowed = 1,
    localparam int GrantCountWidth = $clog2(MaxGrantPerCycle + 1)
) (
    // Only used for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Only used for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,
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
  if (EnableCoverMoreRequestThanAllowed) begin : gen_more_request_than_allowed_cover
    `BR_COVER_INTG(more_request_than_allowed_c, $countones(request) > grant_allowed)
  end else begin : gen_more_request_than_allowed_assert
    `BR_ASSERT_INTG(no_more_request_than_allowed_a, $countones(request) <= grant_allowed)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [MaxGrantPerCycle-1:0][NumRequesters-1:0] grant_ordered_unqual;

  br_enc_priority_encoder #(
      .NumRequesters(NumRequesters),
      .NumResults(MaxGrantPerCycle)
  ) br_enc_priority_encoder_inst (
      .clk(clk),
      .rst(rst),
      .in (request),
      .out(grant_ordered_unqual)
  );

  for (genvar i = 0; i < MaxGrantPerCycle; i++) begin : gen_grant_ordered
    assign grant_ordered[i] = (grant_allowed > i) ? grant_ordered_unqual[i] : '0;
  end

  always_comb begin
    grant = '0;
    grant_count = '0;
    for (int i = 0; i < MaxGrantPerCycle; i++) begin
      grant |= grant_ordered[i];
      grant_count += |grant_ordered[i];
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

endmodule
