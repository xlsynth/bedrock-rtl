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

// Bedrock-RTL Flow Demux with Multihot valid (Unstable)
//
// A dataflow pipeline demux with explicit multihot valid.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when the
// corresponding ready signal and valid signal are both 1 on the same cycle
// for all selected outputs. Otherwise, the stage is stalled.
//
// This is a purely combinational module with 0 delay.
//
// It is called "unstable" because the pop interface is not guaranteed
// to follow the ready-valid stability convention, because the multihot
// valid input could change while the selected pop interfaces are
// backpressuring.
//
// TODO(mgottscho): Write spec doc

`include "br_asserts_internal.svh"

module br_flow_demux_multihot_unstable #(
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

    // Multihot select can potentially change independently of the push and pop interfaces,
    // which is why this module is called "unstable": if the select changes while the connected
    // pop interface is backpressuring, then the ready-valid stability guarantee will be
    // violated on that previously selected pop interfaces.
    input logic [NumFlows-1:0] multihot_select,

    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    input  logic [NumFlows-1:0]            pop_ready,
    // These are labeled explicitly as unstable so that users understand
    // they may not rigorously follow the ready-valid stability guarantee (unless
    // the select signal is used in a more constrained fashion).
    output logic [NumFlows-1:0]            pop_valid_unstable,
    output logic [NumFlows-1:0][Width-1:0] pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_must_be_at_least_two_a, NumFlows >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
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
  logic [NumFlows-1:0] push_valid_multihot;
  // The ternary expression is needed to ensure pop_valid_unstable is 0 (and not X)
  // when multihot_select is X and push_valid is 0.
  assign push_valid_multihot = push_valid ? multihot_select : '0;

  // Replicate pop_data to all flows; this is okay since pop_data[i]
  // is only valid when pop_valid_unstable[i] is high.
  always_comb begin
    for (int i = 0; i < NumFlows; i++) begin
      pop_data_unstable[i] = push_data;
    end
  end

  always_comb begin
    push_ready = '1;
    for (int i = 0; i < NumFlows; i++) begin
      if (push_valid_multihot[i]) begin
        push_ready &= pop_ready[i];
      end
    end
  end

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flows
    always_comb begin
      pop_valid_unstable[i] = push_valid_multihot[i];
      for (int j = 0; j < NumFlows; j++) begin
        if (i != j) begin
          // Invalidate when any valid output is not ready
          pop_valid_unstable[i] &= !(push_valid_multihot[j] && !pop_ready[j]);
        end
      end
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  for (genvar i = 0; i < NumFlows; i++) begin : gen_pop_unstable_checks
    if (EnableAssertPushValidStability) begin : gen_stable_push_valid
      `BR_ASSERT_IMPL(pop_valid_instability_caused_by_select_a,
                      ##1 !pop_ready[i] && $stable(
                          pop_ready[i]
                      ) && $fell(
                          pop_valid_unstable[i]
                      ) |-> !$stable(
                          multihot_select
                      ))
      if (EnableAssertPushDataStability) begin : gen_stable_push_data
        `BR_ASSERT_IMPL(pop_data_instability_caused_by_select_a,
                        ##1 !pop_ready[i] && pop_valid_unstable[i] && $stable(
                            pop_ready[i]
                        ) && $stable(
                            pop_valid_unstable
                        ) && !$stable(
                            pop_data_unstable[i]
                        ) |-> !$stable(
                            multihot_select
                        ))
      end
    end
  end

  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      // We know that the pop valid and data can be unstable.
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

endmodule : br_flow_demux_multihot_unstable
