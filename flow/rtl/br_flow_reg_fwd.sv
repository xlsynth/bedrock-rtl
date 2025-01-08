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

// Bedrock-RTL Flow Register (Forward Variant)
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

module br_flow_reg_fwd #(
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = 1,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic             pop_valid_next;
  logic             pop_data_load_enable;
  logic [Width-1:0] pop_data_next;

  assign push_ready = pop_ready || !pop_valid;
  assign pop_valid_next = push_valid || !push_ready;

  `BR_REG(pop_valid, pop_valid_next)

  assign pop_data_load_enable = push_ready && push_valid;
  assign pop_data_next = push_data;

  // No reset necessary because pop_valid qualifies the value of pop_data.
  `BR_REGLN(pop_data, pop_data_next, pop_data_load_enable)

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

  // Check that the datapath has 1 cycle cut-through delay.
  `BR_ASSERT_IMPL(cutthrough_1_delay_a,
                  ##1 push_ready && push_valid |=> pop_valid && pop_data == $past(push_data))

  // Check that that the backpressure path is combinational (0 delay).
  `BR_ASSERT_IMPL(backpressure_0_delay_a, pop_ready |-> push_ready)

endmodule : br_flow_reg_fwd
