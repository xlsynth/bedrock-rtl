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
// A dataflow pipeline mux with explicit binary select.
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
// It is called "unstable" because the pop interface is not guaranteed
// to follow the ready-valid stability convention, because the select
// input could change while the selected push interface is backpressured.
//
// TODO(mgottscho): Write spec doc

`include "br_asserts_internal.svh"

module br_flow_mux_select_unstable #(
    // Must be at least 2
    parameter int NumFlows = 2,
    // Must be at least 1
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input logic [$clog2(NumFlows)-1:0] select,

    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid_unstable,
    output logic [Width-1:0] pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_must_be_at_least_two_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  `BR_ASSERT_INTG(select_in_range_a, select < NumFlows)

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
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

  // Lint waivers are safe because we assert select is always in range.
  // ri lint_check_waive VAR_SHIFT TRUNC_LSHIFT
  assign push_ready = pop_ready << select;
  // ri lint_check_waive VAR_INDEX_READ
  assign pop_valid_unstable = push_valid[select];
  // ri lint_check_waive VAR_INDEX_READ
  assign pop_data_unstable = push_data[select];

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableAssertPushValidStability) begin : gen_stable_push_valid
    `BR_ASSERT_IMPL(
        pop_valid_instability_caused_by_select_a,
        ##1 !pop_ready && $stable(pop_ready) && $fell(pop_valid_unstable) |-> !$stable(select))
    if (EnableAssertPushDataStability) begin : gen_stable_push_data
      `BR_ASSERT_IMPL(pop_data_instability_caused_by_select_a,
                      ##1 !pop_ready && pop_valid_unstable && $stable(
                          pop_ready
                      ) && $stable(
                          pop_valid_unstable
                      ) && !$stable(
                          pop_data_unstable
                      ) |-> !$stable(
                          select
                      ))
    end
  end

  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(1),
      // We know that pop valid and pop data can be unstable.
      .EnableAssertValidStability(0),
      .EnableAssertDataStability(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data (pop_data_unstable)
  );

endmodule : br_flow_mux_select_unstable
