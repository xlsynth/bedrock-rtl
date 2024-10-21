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

// Bedrock-RTL Flow Register (Reverse Variant)
//
// A dataflow pipeline register that behaves like a 1-entry
// FIFO. Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_flow_reg_rev #(
    // Must be at least 1
    parameter int BitWidth = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    output logic                push_ready,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    input  logic                pop_ready,
    output logic                pop_valid,
    output logic [BitWidth-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, BitWidth >= 1)

  // Assert that under push-side backpressure conditions,
  // the pipeline register correctly stalls upstream.
  // That is, on any given cycle, if push_valid is 1 and push_ready
  // is 0, then assert that on the following cycle push_valid is
  // still 1 and push_data has not changed. In other words,
  // we are checking that the input stimulus abides by the push-side
  // ready-valid interface protocol.
  `BR_ASSERT_INTG(push_backpressure_a, !push_ready && push_valid |=> push_valid && $stable
                                       (push_data))

  // Assert that if push_valid is 1, then push_data must be known (not X).
  // This is not strictly a required integration check, because the module implementation
  // will still function correctly even if push_data is unknown (X).
  // However, under the ready-valid protocol convention where push_data is stable while
  // backpressured, unknown values are by definition not stable and therefore violate the
  // protocol requirement.
  `BR_ASSERT_INTG(push_data_known_a, push_valid |-> !$isunknown(push_data))

  // Assert that if pop_valid is 1, pop_ready must eventually be 1.
  `BR_ASSERT_INTG(eventually_pop_ready_a, pop_valid |-> ##[0:$] pop_ready)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // push_ready is registered. In this implementation it also
  // serves as meaning "empty." So therefore !push_ready means
  // "register valid" or "full."
  //
  // When the register is empty, the bypass path is active, so
  // that push_valid and push_data flow directly to pop_valid
  // and pop_data in the same cycle (0 latency). When pop_ready
  // However, when pop_ready is low, then the internal register
  // captures the data (like a 1-deep skid buffer).

  logic [BitWidth-1:0] reg_data;

  assign pop_valid = !push_ready || push_valid;
  assign pop_data  = push_ready ? push_data : reg_data;

  `BR_REGI(push_ready, pop_ready || (push_ready && !push_valid), 1'b1)

  // No reset necessary for reg_data because !push_ready qualifies the value of reg_data.
  // And push_ready resets to 1'b1, so the unknown value of reg_data doesn't matter.
  `BR_REGLN(reg_data, push_data, !pop_ready && push_valid)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Assert that under pop-side backpressure conditions,
  // the pipeline register correctly stalls downstream.
  // That is, on any given cycle, if pop_valid is 1 and pop_ready is 0,
  // then assert that on the following cycle pop_valid is still 1 and
  // pop_data has not changed. In other words, we are checking that
  // the implementation absides by the pop-side ready-valid interface protocol.
  `BR_ASSERT_IMPL(pop_backpressure_a, !pop_ready && pop_valid |=> pop_valid && $stable(pop_data))

  // This module must be ready to accept pushes out of reset.
  `BR_ASSERT_IMPL(reset_a, $fell(rst) |-> push_ready)

  // As noted in the integration checks, unknown pop_data can be checked with X-propagation tools.
  // However, if we already check the integration that push_valid |-> !$isunknown(push_data), then
  // we also know this module must also have known pop_data whenever pop_valid is 1.
  `BR_ASSERT_IMPL(pop_data_known_a, pop_valid |-> !$isunknown(pop_data))

  // Check that the datapath has 0 cycle cut-through delay.
  `BR_ASSERT_IMPL(cutthrough_0_delay_a,
                  push_ready && push_valid && pop_ready |-> pop_valid && pop_data == push_data)

  // Check that that the backpressure path has 1 cycle delay.
  `BR_ASSERT_IMPL(backpressure_1_delay_a, pop_ready |=> push_ready)

endmodule : br_flow_reg_rev
