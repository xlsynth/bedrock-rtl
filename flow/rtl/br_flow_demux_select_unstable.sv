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

// Bedrock-RTL Flow Demux with Select
//
// A dataflow pipeline demux with explicit select.
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

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_flow_demux_select_unstable #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 1
    parameter int BitWidth = 1
) (
    input logic clk,  // Used only for assertions
    input logic rst,  // Used only for assertions

    input logic [$clog2(NumRequesters)-1:0] select,

    output logic                push_ready,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    input  logic [NumRequesters-1:0]               pop_ready,
    output logic [NumRequesters-1:0]               pop_valid,
    output logic [NumRequesters-1:0][BitWidth-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(NumRequestersMustBeAtLeastTwo_A, NumRequesters >= 2);
  `BR_ASSERT_STATIC(BitWidthMustBeAtLeastOne_A, BitWidth >= 1);

  // TODO(mgottscho): Add integration checks on ready-valid compliance and on stability of select.

  `BR_ASSERT_INTG(select_in_range_intg_A, select < NumRequesters)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign push_ready = pop_ready[select];
  assign pop_valid  = push_valid << select;
  // Replicate pop_data to all requesters; this is okay since pop_data[i]
  // is only valid when pop_valid[i] is high.
  always_comb begin
    for (int i = 0; i < NumRequesters; i++) begin
      pop_data[i] = push_data;
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // TODO(mgottscho): Add implementation checks on ready-valid compliance.

endmodule : br_flow_demux_select_unstable
