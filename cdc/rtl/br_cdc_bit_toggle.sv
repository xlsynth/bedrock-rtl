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

// CDC synchronizer for a single bit level signal.

`include "br_registers.svh"
`include "br_asserts.svh"
`include "br_gates.svh"
module br_cdc_bit_toggle #(
    // Number of synchronization stages. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumStages = 3,
    // If 1, add a flop on the source clock before the synchronizer
    parameter bit AddSourceFlop = 1
) (
    // Used for simulation delay modeling only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_clk,
    // Used for assertion only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_rst,
    input logic src_bit,

    input  logic dst_clk,
    // Used for assertion only
    // ri lint_check_waive INPUT_NOT_READ NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic dst_rst,
    output logic dst_bit
);

  // Integration Assertions
  `BR_ASSERT_STATIC(num_stages_must_be_at_least_one_a, NumStages >= 1)

  // Implementation
  logic src_bit_internal, src_bit_internal_maxdel;

  if (AddSourceFlop) begin : gen_src_flop
    `BR_REGNX(src_bit_internal, src_bit, src_clk)
  end else begin : gen_src_passthrough
    assign src_bit_internal = src_bit;
  end

  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL(src_bit_internal_maxdel, src_bit_internal)
  // ri lint_check_on ONE_CONN_PER_LINE

  // TODO: Add simulation delay modeling

  br_gate_cdc_sync #(
      .NumStages(NumStages)
  ) br_gate_cdc_sync (
      .clk(dst_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .in(src_bit_internal_maxdel),
      .out(dst_bit)
  );

endmodule
