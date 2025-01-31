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

// Bedrock-RTL Count Ones

`include "br_asserts_internal.svh"

module br_enc_countones #(
    parameter int Width = 1,  // Must be at least 1
    localparam int CountWidth = $clog2(Width + 1)
) (
    input logic [Width-1:0] in,
    output logic [CountWidth-1:0] count
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  always_comb begin
    count = 0;
    for (int i = 0; i < Width; i++) begin
      count += in[i];
    end
  end

endmodule : br_enc_countones
