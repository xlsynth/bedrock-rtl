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
// TODO(mgottscho): Write spec

`include "br_asserts_internal.svh"

module br_enc_bin2onehot #(
    parameter int NumValues = 2,  // Must be at least 2
    parameter int EnableInputRangeCheck = 1,
    parameter int BinWidth = $clog2(NumValues)
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
  `BR_ASSERT_STATIC(num_values_gte_2_a, NumValues >= 2)
  `BR_ASSERT_STATIC(binwidth_gte_log2_num_values_a, BinWidth >= $clog2(NumValues))
  if (EnableInputRangeCheck) begin : gen_in_range_check
    `BR_ASSERT_INTG(in_within_range_a, in_valid |-> in < NumValues)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    out = '0;
    if (in_valid) begin
      for (int i = 0; i < NumValues; i++) begin
        if (in == i) begin
          out[i] = 1'b1;
          break;
        end
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableInputRangeCheck) begin : gen_out_onehot
    `BR_ASSERT_IMPL(out_onehot_a, in_valid |-> $onehot(out))
  end
endmodule : br_enc_bin2onehot
