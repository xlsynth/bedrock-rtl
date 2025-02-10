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

// Bedrock-RTL Dynamic Priority Encoder
//
// This module implements a priority encoder in which the priority
// of inputs is specified dynamically at runtime.
// The user provides a onehot-encoded vector `lowest_prio`.
// The bit set in `lowest_prio` will be given the lowest priority.
// The priority of bits then goes from the next more significant bit
// up to the most significant bit and wrapping back to the LSB.
// That is, if the bit set is `lp`, the highest priority bit is
// in `in[lp+1]`, followed by `in[lp+2]`, up to `in[NumRequesters-1]`.
// After that, it wraps to `in[0]`, `in[1]`, up to `in[lp]`.
// If `lp` happens to be `NumRequesters-1`, then the highest priority
// bit is `in[0]` and this module functions the same as a regular
// priority encoder with `MsbHighestPriority` set to 0.

`include "br_asserts_internal.svh"

module br_enc_priority_dynamic #(
    parameter int NumRequesters = 2,
    parameter int NumResults = 1
) (
    input logic clk,
    input logic rst,
    input logic [NumRequesters-1:0] in,
    input logic [NumRequesters-1:0] lowest_prio,
    output logic [NumResults-1:0][NumRequesters-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_num_results_a, NumResults >= 1)
  `BR_ASSERT_STATIC(legal_num_requesters_a, NumRequesters >= NumResults)

  `BR_ASSERT_INTG(lowest_prio_onehot_a, $onehot(lowest_prio))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Priority mask is the unary encoding of lowest_prio.
  // That is, the bit set in lowest_prio and all the ones
  // less significant than it will be set.
  // For the priority encoding, any request i for which
  // priority_mask[i] is set will have lower priority than
  // the requesters for which priority_mask[i] is not set.
  logic [NumRequesters-1:0] priority_mask;
  logic [NumRequesters-1:0] in_high_prio;
  logic [NumRequesters-1:0] in_low_prio;

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_priority_mask
    assign priority_mask[i] = |lowest_prio[NumRequesters-1:i];
  end

  assign in_low_prio  = in & priority_mask;
  assign in_high_prio = in & ~priority_mask;

  // If there are as many results as requesters,
  // we only need NumRequesters-1 results from the
  // priority encoder. The last result will just be the
  // input with all the previous results masked off.
  localparam int InternalNumResults = br_math::min2(NumResults, NumRequesters - 1);

  logic [InternalNumResults-1:0][2*NumRequesters-1:0] out_internal;

  // Create a double-wide priority encoder with the
  // high priority inputs in the lower half and the
  // low priority inputs in the upper half.
  br_enc_priority_encoder #(
      .NumRequesters(2 * NumRequesters),
      .NumResults(InternalNumResults)
  ) br_enc_priority_encoder_inst (
      .clk,
      .rst,
      .in ({in_low_prio, in_high_prio}),
      .out(out_internal)
  );

  // To get the final result, fold the double-wide results
  // together using bitwise OR.
  for (genvar i = 0; i < InternalNumResults; i++) begin : gen_out
    assign out[i] =
        out_internal[i][2*NumRequesters-1:NumRequesters] |
        out_internal[i][NumRequesters-1:0];
  end

  // If there are as many results as requesters, the last result just gets
  // what's left over in the input after the previous results have been masked
  // off.
  if (NumResults == NumRequesters) begin : gen_last_out
    always_comb begin
      out[NumResults-1] = in;

      for (int i = 0; i < InternalNumResults; i++) begin : gen_last_out_checks
        out[NumResults-1] &= ~out[i];
      end
    end
  end

  //------------------------------------------
  // Implementation Checks
  //------------------------------------------
  for (genvar i = 0; i < NumResults; i++) begin : gen_out_checks
    `BR_ASSERT_IMPL(out_onehot0_a, $onehot0(out[i]))
  end

endmodule
