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
//
// Synchronizer for gray-encoded counts that adds some useful integration
// assertions.

`include "br_asserts_internal.svh"
`include "br_gates.svh"

module br_cdc_fifo_gray_count_sync #(
    // Width of the gray-encoded count. Must be at least 2.
    parameter int CountWidth = 2,
    // Number of synchronization stages. Must be at least 1.
    parameter int NumStages  = 3
) (
    // Used for assertions only
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_clk,
    // Used for assertions only
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic src_rst,
    input logic [CountWidth-1:0] src_count_gray,

    input logic dst_clk,
    // Used for assertions only
    // ri lint_check_waive HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic dst_rst,
    output logic [CountWidth-1:0] dst_count_gray
);
  // Integration Assertions

  `BR_ASSERT_STATIC(legal_count_width_a, CountWidth >= 2)
  `BR_ASSERT_STATIC(legal_num_stages_a, NumStages >= 1)

  `BR_ASSERT_CR_IMPL(single_bit_change_a, $onehot0(src_count_gray ^ $past(src_count_gray)),
                     src_clk, src_rst)

  // Implementation

  logic [CountWidth-1:0] src_count_gray_maxdel;

  // Tag this signal as needing max delay checks
  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL_BUS(src_count_gray_maxdel, src_count_gray, CountWidth)
  // ri lint_check_on ONE_CONN_PER_LINE

  for (genvar i = 0; i < CountWidth; i++) begin : gen_cdc_sync
    br_cdc_bit_toggle #(
        .AddSourceFlop(0),  // Assume flopped externally
        .NumStages(NumStages)
    ) br_cdc_bit_toggle_inst (
        .src_clk,
        .src_rst,
        .src_bit(src_count_gray_maxdel[i]),
        .dst_clk,
        .dst_rst,
        .dst_bit(dst_count_gray[i])
    );
  end

endmodule : br_cdc_fifo_gray_count_sync
