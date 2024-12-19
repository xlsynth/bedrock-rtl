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

// Bedrock-RTL Onehot to Binary Encoder
//
// Converts a 0-based onehot-encoded input to a multihot binary-encoded output.
// Purely combinational (zero delay and stateless).
//
// For convenience, this is actually a "onehot-0" to binary encoder.
// When input is all 0s, out_valid is driven to '0.
//
// For example:
//
// NumValues = 5
//
// in       |       out
// --------------------
//    normal cases
// --------------------
// 5'b00001 |    3'b000
// 5'b00010 |    3'b001
// 5'b00100 |    3'b010
// 5'b01000 |    3'b011
// 5'b10000 |    3'b100
// --------------------
//    special case
// --------------------
// 5'b00000 |    3'b000
// --------------------
//   illegal inputs
// --------------------
// 5'b00101 | undefined
// 5'b11010 | undefined
// 5'b11111 | undefined
// ...
//
// The BinWidth parameter sets the width of the binary-encoded value.
// It must be at least $clog2(NumValues) but may be set larger than the minimum
// width and the result will be zero-extended.

`include "br_asserts_internal.svh"

module br_enc_onehot2bin #(
    parameter int NumValues = 2,  // Must be at least 2
    // Width of the binary-encoded value. Must be at least $clog2(NumValues).
    parameter int BinWidth = $clog2(NumValues)
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 clk,        // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                 rst,        // Used only for assertions
    input  logic [NumValues-1:0] in,
    output logic                 out_valid,
    output logic [ BinWidth-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_values_gte_2_a, NumValues >= 2)
  `BR_ASSERT_STATIC(binwidth_gte_log2_num_values_a, BinWidth >= $clog2(NumValues))
  `BR_ASSERT_INTG(in_onehot_a, $onehot0(in))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign out_valid = |in;
  always_comb begin
    out = '0; // ri lint_check_waive CONST_OUTPUT
    for (int i = 1; i < NumValues; i++) begin
      // If multiple bits are set, this is undefined behavior.
      if (in[i]) begin
        // This waiver is not a problem so long as we are not doing
        // anything close to a 32-bit onehot2bin..
        // ri lint_check_waive INTEGER ASSIGN_SIGN SIGNED_SIZE_CAST
        out |= BinWidth'(i); // ri lint_check_waive CONST_OUTPUT
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(out_within_range_a, out < NumValues)

endmodule : br_enc_onehot2bin
