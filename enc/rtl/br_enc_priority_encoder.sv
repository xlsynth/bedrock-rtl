// Copyright 2024 The Bedrock-RTL Authors
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

// TODO(mgottscho): Write spec

`include "br_asserts_internal.svh"

module br_enc_priority_encoder #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input  logic [NumRequesters-1:0] in,
    output logic [NumRequesters-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_requesters_at_least_two_a, NumRequesters >= 2)

  // TODO(mgottscho): Write a cover point that multiple inputs are concurrently active

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    out = '0;
    for (int i = 0; i < NumRequesters; i++) begin
      // Lowest index is highest priority
      if (in[i]) begin
        out[i] = 1'b1;
        break;
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_COMB_IMPL(out_onehot0_a, $onehot0(out))
  `BR_ASSERT_COMB_IMPL(out_lowest_max_priority_a, in[0] == out[0])
  `BR_ASSERT_COMB_IMPL(
      out_highest_min_priority_a,
      out[NumRequesters-1] |-> in[NumRequesters-1] && (|in[NumRequesters-2:0] == '0))

endmodule : br_enc_priority_encoder
