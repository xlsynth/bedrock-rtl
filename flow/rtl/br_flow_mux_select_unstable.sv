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

// Bedrock-RTL Flow Mux with Select (Unstable)
//
// A dataflow pipeline mux with explicit select.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// This is a purely combinational module with 0 delay.
//
// TODO(mgottscho): Write spec doc

`include "br_asserts_internal.svh"

module br_flow_mux_select_unstable #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 1
    parameter int BitWidth = 1
) (
    // Used only for assertions
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Used only for assertions
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input logic [$clog2(NumRequesters)-1:0] select,

    output logic [NumRequesters-1:0]               push_ready,
    input  logic [NumRequesters-1:0]               push_valid,
    input  logic [NumRequesters-1:0][BitWidth-1:0] push_data,

    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [BitWidth-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_requesters_must_be_at_least_two_a, NumRequesters >= 2)
  `BR_ASSERT_STATIC(bitwidth_gte_1_a, BitWidth >= 1)

  // TODO(mgottscho): Add integration checks on ready-valid compliance and
  // on stability of push_select.

  `BR_ASSERT_INTG(select_in_range_a, select < NumRequesters)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign push_ready = pop_ready << select;
  assign pop_valid  = push_valid[select];
  assign pop_data   = push_data[select];

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // TODO(mgottscho): Add implementation checks on ready-valid compliance.

endmodule : br_flow_mux_select_unstable
