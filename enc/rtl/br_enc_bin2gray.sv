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

// Bedrock-RTL Binary-to-Gray Converter

`include "br_asserts_internal.svh"

module br_enc_bin2gray #(
    parameter int BitWidth = 2  // Must be at least 2
) (
    input  logic [BitWidth-1:0] bin,
    output logic [BitWidth-1:0] gray
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_gte_2_a, BitWidth >= 2)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [BitWidth-1:0] bin_offset;

  assign bin_offset = {1'b0, bin[BitWidth-1:1]};
  assign gray = bin_offset ^ bin;

endmodule : br_enc_bin2gray
