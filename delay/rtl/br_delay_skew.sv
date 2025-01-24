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

// Bedrock-RTL Delay Line Skew (Valid to Valid-Next)
//
// Retimes a delay line using aligned valid/data to instead
// use valid-next/data (i.e., valid runs one cycle ahead of data).
// Adds 1 cycle of latency to the datapath to allow the valid to run ahead.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_delay_skew #(
    parameter int Width = 1,  // Must be at least 1
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Positive edge-triggered clock.
    input  logic             clk,
    input  logic             in_valid,
    input  logic [Width-1:0] in,
    output logic             out_valid_next,
    output logic [Width-1:0] out
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(width_must_be_at_least_one_a, Width >= 1)

  `BR_COVER_INTG(in_valid_c, in_valid)

  if (EnableAssertFinalNotValid) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_not_in_valid_a, !in_valid)
    `BR_ASSERT_FINAL(final_not_out_valid_next_a, !out_valid_next)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign out_valid_next = in_valid;
  `BR_REGLN(out, in, in_valid)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(valid_delay_a, out_valid_next === in_valid)
  `BR_ASSERT_IMPL(data_delay_a, in_valid |=> out === $past(in))

endmodule : br_delay_skew
