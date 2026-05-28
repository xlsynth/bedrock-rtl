// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Dynamic Priority Encoder FPV monitor
//
// Testplan:
// - Design intent:
//   - `br_enc_priority_dynamic` selects up to `NumResults` one-hot winners from
//     `in`.
//   - `lowest_prio` is one-hot and marks the lowest-priority requester.
//   - Priority starts at the next more-significant requester after
//     `lowest_prio`, walks toward the MSB, then wraps to bit 0 and continues
//     through the lowest-priority requester.
//   - When `lowest_prio[NumRequesters-1]` is set, priority order starts at
//     requester 0 and matches a normal LSB-highest priority encoder.
// - Input assumptions:
//   - Legal parameters require `NumResults >= 1` and
//     `NumRequesters >= NumResults`.
//   - `lowest_prio` must be one-hot.
//   - `in` is an unconstrained request vector.
// - Output behavior to verify in the full monitor implementation:
//   - Each `out[i]` is one-hot or zero.
//   - No `out[i]` grants a requester whose `in` bit is low.
//   - Grant vectors are mutually exclusive.
//   - Earlier result slots grant higher-priority active requesters than later
//     result slots.
//   - If fewer than `NumResults` requests are active, remaining result slots
//     are zero.
//   - If `NumResults == NumRequesters`, all active requesters are eventually
//     represented across the result vector.
// - Covers to add in the full monitor implementation:
//   - Wrap-around priority cases.
//   - All-requesters-active cases.
//   - Fewer-active-requests-than-results cases.

`include "br_asserts.svh"
`include "br_fv.svh"
`include "br_registers.svh"

module br_enc_priority_dynamic_fpv_monitor #(
    parameter int NumRequesters = 2,
    parameter int NumResults = 1
) (
    input logic clk,
    input logic rst,
    input logic [NumRequesters-1:0] in,
    input logic [NumRequesters-1:0] lowest_prio,
    input logic [NumResults-1:0][NumRequesters-1:0] out
);

  localparam int IdxWidth = (NumRequesters > 1) ? $clog2(NumRequesters) : 1;
  localparam int ResultIdxWidth = (NumResults > 1) ? $clog2(NumResults) : 1;
  localparam int RequestCountWidth = $clog2(NumRequesters + 1);
  localparam int ResultCountWidth = $clog2(NumResults + 1);

  // Symbolic non-equal requester indices, constrained by BR_FV_2RAND_IDX below.
  logic [IdxWidth-1:0] req0, req1;
  // Symbolic non-equal result-slot indices, constrained by BR_FV_2RAND_IDX below.
  logic [ResultIdxWidth-1:0] res0, res1;
  logic [IdxWidth-1:0] lowest_prio_idx;
  logic [IdxWidth:0] req0_prio_distance;
  logic [IdxWidth:0] req1_prio_distance;
  logic req0_higher_prio_than_req1;
  logic [RequestCountWidth-1:0] active_count;
  logic [ResultCountWidth-1:0] result_count;
  logic res0_req0_seen;

  // Returns how far `idx` is from `lowest_prio` in the rotated priority order.
  function automatic logic [IdxWidth:0] prio_distance(input logic [IdxWidth-1:0] idx);
    if (idx > lowest_prio_idx) begin
      return {1'b0, idx} - {1'b0, lowest_prio_idx};
    end

    return {1'b0, idx} + (IdxWidth + 1)'(NumRequesters) - {1'b0, lowest_prio_idx};
  endfunction

  always_comb begin
    active_count = '0;
    for (int req_idx = 0; req_idx < NumRequesters; req_idx++) begin
      active_count += RequestCountWidth'(in[req_idx]);
    end
  end

  always_comb begin
    result_count = '0;
    for (int res_idx = 0; res_idx < NumResults; res_idx++) begin
      result_count += ResultCountWidth'(out[res_idx] != '0);
    end
  end

  `BR_FV_IDX(lowest_prio_idx, lowest_prio, NumRequesters)

  always_comb begin
    req0_prio_distance = prio_distance(req0);
    req1_prio_distance = prio_distance(req1);
  end

  // Example with 4 requesters:
  //   lowest_prio = 4'b0010, so requester 1 is lowest priority.
  //   Priority order is 2, 3, 0, 1.
  //   If in = 4'b1011, then active requesters are 3, 1, and 0.
  //   The expected outputs are:
  //     out[0] = 4'b1000  // requester 3
  //     out[1] = 4'b0001  // requester 0
  //     out[2] = 4'b0010  // requester 1
  //   For req0=0 and req1=1, req0_higher_prio_than_req1 is true. Therefore,
  //   pairwise_priority_order_a allows out[2][req1] only because req0 was
  //   already seen in an earlier output slot: out[1] = 4'b0001.
  //   Lower result indices correspond to higher-priority grants.

  // A smaller distance means the requester is seen earlier by the dynamic priority encoder.
  assign req0_higher_prio_than_req1 = req0_prio_distance < req1_prio_distance;

  // Tracks whether requester `req0` has already appeared before symbolic result slot `res0`.
  always_comb begin
    res0_req0_seen = 1'b0;
    for (int res_idx = 0; res_idx < NumResults; res_idx++) begin
      if (res_idx < res0) begin
        res0_req0_seen |= out[res_idx][req0];
      end
    end
  end

  // Assumes the dynamic priority input obeys the DUT integration contract.
  `BR_ASSUME(lowest_prio_onehot_a, $onehot(lowest_prio))

  if (NumRequesters > 1) begin : gen_priority_pair
    `BR_FV_2RAND_IDX(req0, req1, NumRequesters)

    // Checks pairwise dynamic priority ordering at a symbolic result slot.
    `BR_ASSERT(
        pairwise_priority_order_a,
        !(in[req0] && in[req1] && req0_higher_prio_than_req1 && out[res0][req1]) || res0_req0_seen)
  end

  if (NumResults > 1) begin : gen_result_pair
    `BR_FV_2RAND_IDX(res0, res1, NumResults)

    // Checks that no requester appears in more than one symbolic result slot.
    `BR_ASSERT(out_mutually_exclusive_a, (out[res0] & out[res1]) == '0)

    // Checks that a symbolic result slot is either one-hot or empty.
    `BR_ASSERT(out_onehot0_a, $onehot0(out[res0]))

    // Checks that a symbolic result slot grants only active requesters.
    `BR_ASSERT(out_subset_in_a, (out[res0] & ~in) == '0)
  end else begin : gen_single_result
    assign res0 = '0;
    assign res1 = '0;

    // Checks that the only result slot is either one-hot or empty.
    `BR_ASSERT(out_onehot0_a, $onehot0(out[0]))

    // Checks that the only result slot grants only active requesters.
    `BR_ASSERT(out_subset_in_a, (out[0] & ~in) == '0)
  end

  // Checks that the DUT emits exactly one result per active input, capped by NumResults.
  `BR_ASSERT(result_count_a,
             result_count == ((active_count < NumResults) ? active_count : NumResults))

  // Covers the fully contended case where all requesters are active.
  `BR_COVER(all_requesters_active_c, &in)

  if (NumResults > 1) begin : gen_fewer_requests_cover
    // Covers the case where fewer requests are active than result slots.
    `BR_COVER(fewer_requests_than_results_c, (active_count != '0) && (active_count < NumResults))
  end

  if (NumRequesters > 1) begin : gen_wrap_covers
    // Covers a priority wrap from the MSB side back to requester 0.
    `BR_COVER(wrap_priority_c, lowest_prio != (1 << (NumRequesters - 1)) && in[0])
  end

endmodule : br_enc_priority_dynamic_fpv_monitor

bind br_enc_priority_dynamic br_enc_priority_dynamic_fpv_monitor #(
    .NumRequesters(NumRequesters),
    .NumResults(NumResults)
) monitor (.*);
