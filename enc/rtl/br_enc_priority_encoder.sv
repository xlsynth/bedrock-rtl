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

// Bedrock-RTL Priority Encoder
//
// Masks all but the highest priority active request in an input where the
// lowest index is the highest priority.
//
// Can optionally produce more than one result if NumResults is greater than 1.
// If so, out[0] will have the highest priority bit set, out[1] will have the
// second highest priority bit set, etc.

// TODO(mgottscho): Write spec

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_enc_priority_encoder #(
    // Must be at least 2 and greater than NumResults.
    parameter int NumRequesters = 2,
    // Number of onehot results to produce. Must be at least 1.
    parameter int NumResults = 1
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Used only for assertions
    input logic [NumRequesters-1:0] in,
    output logic [NumResults-1:0][NumRequesters-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_results_a, NumResults >= 1)
  `BR_ASSERT_STATIC(legal_num_requesters_a, NumRequesters > NumResults)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  logic [$clog2(NumRequesters+1)-1:0] num_in_hot;

  always_comb begin
    num_in_hot = '0;
    for (int i = 0; i < NumRequesters; i++) begin
      num_in_hot += in[i];
    end
  end

  `BR_COVER_INTG(more_in_hot_than_num_results_c, num_in_hot > NumResults)
`endif
`endif

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Each result is a separate priority search on the input
  // with the bits selected by previous results masked off.
  for (genvar out_idx = 0; out_idx < NumResults; out_idx++) begin : gen_out
    logic [NumRequesters-1:0] in_masked;

    // Generated the masked input
    // Any bit that was set in a previous result
    // should be cleared in the masked input.
    always_comb begin
      in_masked = in;
      // This for loop won't be entered if out_idx is 0
      // This is expected since we just want in_masked to be in
      // ri lint_check_waive LOOP_NOT_ENTERED
      for (int prev_idx = 0; prev_idx < out_idx; prev_idx++) begin
        in_masked &= ~out[prev_idx];
      end
    end

    // in_masked[out_idx-1:0] will always be zero since
    // they would have been claimed by a previous result.
    // out[out_idx][out_idx-1:0] must always be zero
    if (out_idx > 0) begin : gen_out_masked_lsb_tieoff
      // ri lint_check_waive CONST_OUTPUT
      assign out[out_idx][out_idx-1:0] = '0;
      `BR_UNUSED(in_masked[out_idx-1:0])
      `BR_ASSERT_IMPL(in_masked_lsb_zero_a, in_masked[out_idx-1:0] == '0)
    end

    // Generate the onehot result for this stage
    // LSB is highest priority and is set unconditionally
    // if the masked input bit is set.
    assign out[out_idx][out_idx] = in_masked[out_idx];
    for (genvar in_idx = out_idx + 1; in_idx < NumRequesters; in_idx++) begin : gen_out_bit
      // Output is set if the corresponding input bit is set and all lower index
      // bits of the masked input are not set.
      assign out[out_idx][in_idx] = in_masked[in_idx] && (in_masked[in_idx-1:out_idx] == '0);
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  // prev_out[i] is the bitwise OR of all out from 0 to i-1
  logic [NumResults-1:0][NumRequesters-1:0] prev_out;
  // num_prev_out[i] is the number of bits set in prev_out[i]
  logic [NumResults-1:0][$clog2(NumRequesters+1)-1:0] num_prev_out;

  for (genvar out_idx = 0; out_idx < NumResults; out_idx++) begin : gen_out_impl_checks
    always_comb begin
      prev_out[out_idx] = '0;
      num_prev_out[out_idx] = '0;
      // ri lint_check_waive LOOP_NOT_ENTERED
      for (int i = 0; i < out_idx; i++) begin
        prev_out[out_idx] |= out[i];
        num_prev_out[out_idx] += |out[i];
      end
    end

    // Each output needs to be onehot
    `BR_ASSERT_IMPL(out_onehot0_a, $onehot0(out[out_idx]))
    // The highest priority bit of the output must be set if the corresponding
    // input bit is set and it was not taken by a previous result.
    `BR_ASSERT_IMPL(out_lowest_max_priority_a,
                    (in[out_idx] && !prev_out[out_idx][out_idx]) |-> out[out_idx][out_idx])
    for (
        genvar in_idx = out_idx + 1; in_idx < NumRequesters; in_idx++
    ) begin : gen_msb_input_impl_checks
      // A bit in out can only be set if the higher priority bits of the input
      // are not set or were taken by a higher priority output.
      `BR_ASSERT_IMPL(
          no_out_if_higher_prio_in_a,
          out[out_idx][in_idx] |-> ((in[in_idx-1:0] & ~prev_out[out_idx][in_idx-1:0]) == '0))
    end

    if (out_idx > 0) begin : gen_secondary_out_impl_checks
      // For each result, there cannot be a bit set if there weren't bits set in
      // all previous results.
      `BR_ASSERT_IMPL(no_out_without_prev_out_a,
                      (|out[out_idx]) |-> (num_prev_out[out_idx] == out_idx))

      for (
          genvar in_idx = out_idx; in_idx < (NumRequesters - 1); in_idx++
      ) begin : gen_secondary_out_per_input_impl_checks
        // If a bit is set in a secondary output, the higher priority outputs
        // must not have taken an input of lower priority.
        `BR_ASSERT_IMPL(
            out_lower_prio_than_prev_out_a,
            out[out_idx][in_idx] |-> (prev_out[out_idx][NumRequesters-1:in_idx+1] == '0))
      end
    end
  end

  if (NumResults > 1) begin : gen_no_collision_check
    logic [NumRequesters-1:0] out_intersect;

    always_comb begin
      out_intersect = out[0];
      for (int i = 1; i < NumResults; i++) begin
        out_intersect &= out[i];
      end
    end

    `BR_ASSERT_IMPL(no_out_collision_a, out_intersect == '0)
  end
`endif
`endif

endmodule : br_enc_priority_encoder
