// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Demux with Select (Unstable)
//
// A dataflow pipeline demux with explicit binary select.
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
// input could change while the selected pop interface is backpressuring.

`include "br_asserts_internal.svh"

module br_flow_demux_select_unstable #(
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
    // If 1, assert that select is stable when push is backpressured.
    // If 0, cover that select can be unstable.
    parameter bit EnableAssertSelectStability = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int SelectWidth = $clog2(NumFlows)
) (
    // Used only for assertions
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high reset. Used only for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    // Select can potentially change independently of the push and pop interfaces, which
    // is why this module is called "unstable": if the select changes while the connected
    // pop interface is backpressuring, then the ready-valid stability guarantee will be
    // violated on that previously selected pop interface.
    input logic [SelectWidth-1:0] select,

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
  `BR_ASSERT_STATIC(select_stability_implies_valid_stability_a,
                    !(EnableAssertSelectStability && !EnableAssertPushValidStability))

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  if (EnableCoverPushBackpressure && EnableAssertPushValidStability) begin : gen_select_checks
    if (EnableAssertSelectStability) begin : gen_select_stability_check
      `BR_ASSERT_INTG(select_stable_a,
                      (!push_ready && push_valid) |=> push_valid && $stable(select))
    end else begin : gen_select_instability_cover
      `BR_COVER_INTG(select_unstable_c,
                     !push_ready && push_valid ##1 push_valid && !$stable(select))
    end
  end

  `BR_ASSERT_INTG(select_known_and_in_range_a, push_valid |-> (!$isunknown(select)
                                               && select < NumFlows))

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Lint waivers are safe because we assert select is always in range.
  // ri lint_check_waive VAR_INDEX_READ
  assign push_ready = pop_ready[select];
  // The ternary expression is needed to ensure pop_valid_unstable is 0 (and not X)
  // when select is X and push_valid is 0.
  // ri lint_check_waive VAR_SHIFT TRUNC_LSHIFT
  assign pop_valid_unstable = push_valid ? (push_valid << select) : '0;
  // Replicate pop_data to all flows; this is okay since pop_data[i]
  // is only valid when pop_valid_unstable[i] is high.
  always_comb begin
    for (int i = 0; i < NumFlows; i++) begin
      pop_data_unstable[i] = push_data;
    end
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  if (EnableCoverPushBackpressure && EnableAssertPushValidStability && !EnableAssertSelectStability)
  begin : gen_stable_push_valid
    for (genvar i = 0; i < NumFlows; i++) begin : gen_pop_unstable_checks
      `BR_ASSERT_IMPL(
          pop_valid_instability_caused_by_select_a,
          (!pop_ready[i] && pop_valid_unstable[i]) ##1 !pop_valid_unstable[i] |-> !$stable(select))
    end
  end

  br_flow_checks_valid_data_impl #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      // Pop valid and data can only be stable if select is stable.
      .EnableAssertValidStability(EnableAssertPushValidStability && EnableAssertSelectStability),
      .EnableAssertDataStability(EnableAssertPushDataStability && EnableAssertSelectStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data (pop_data_unstable)
  );

endmodule : br_flow_demux_select_unstable
