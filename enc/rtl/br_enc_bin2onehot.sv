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

// Bedrock-RTL Binary to Onehot Encoder
//
// Converts a 0-based multihot binary-encoded input to a onehot-encoded output.
// Purely combinational (zero delay and stateless).
//
// The in_valid input can be used to qualify the input (all outputs are driven
// to 0 when in_valid is 0). It can be tied to 1'b1 when not needed.
//
// For example:
//
// NumValues = 5
//
// in      |       out
// -------------------
//  3'b000 |  5'b00001
//  3'b001 |  5'b00010
//  3'b010 |  5'b00100
//  3'b011 |  5'b01000
//  3'b100 |  5'b10000
// -------------------
//  3'b101 | undefined
//  3'b110 | undefined
//  3'b111 | undefined
//
//
// The BinWidth parameter sets the width of the binary-encoded value.
// It must be at least $clog2(NumValues) but may be set larger than the minimum
// width. Irrespective of the width, the input binary must be in the allowed range
// 0 <= in < NumValues.

`include "br_asserts_internal.svh"

module br_enc_bin2onehot #(
    parameter int NumValues = 2,  // Must be at least 1
    parameter int EnableInputRangeCheck = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // Width of the binary-encoded value. Must be at least $clog2(NumValues).
    parameter int BinWidth = br_math::clamped_clog2(NumValues)
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,  // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,  // Used only for assertions
    input logic [BinWidth-1:0] in,
    input logic in_valid,
    output logic [NumValues-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_values_gte_2_a, NumValues >= 1)
  `BR_ASSERT_STATIC(binwidth_gte_log2_num_values_a, BinWidth >= br_math::clamped_clog2(NumValues))
  if (EnableInputRangeCheck) begin : gen_in_range_check
    `BR_ASSERT_INTG(in_within_range_a, in_valid |-> in < NumValues)
  end

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    for (int i = 0; i < NumValues; i++) begin
      out[i] = in_valid && (in == i);
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableInputRangeCheck) begin : gen_out_onehot
    `BR_ASSERT_IMPL(out_onehot_a, in_valid |-> $onehot(out))
  end
endmodule : br_enc_bin2onehot
