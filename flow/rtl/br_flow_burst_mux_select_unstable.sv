// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Burst Mux with Select (Unstable)
//
// A dataflow pipeline mux with explicit binary select and burst ownership.
// Once a selected flow wins a non-terminal beat, that flow remains selected
// until it later presents push_last alongside push_valid.
//
// This is a combinational data-path module with 0 delay from the active push
// flow to pop, plus internal state that tracks the selected burst owner.
//
// It is called "unstable" because before a burst is captured, the pop interface
// is not guaranteed to follow ready-valid stability if select changes while the
// selected push flow is backpressured.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_flow_burst_mux_select_unstable #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that select will not change when the selected push flow is backpressured
    // before a burst owner has been captured. Otherwise, cover that select can be unstable.
    parameter bit EnableAssertSelectStability = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int SelectWidth = br_math::clamped_clog2(NumFlows)
) (
    // Used only for assertions.
    input logic clk,
    // Synchronous active-high reset. Used only for assertions and burst ownership state.
    input logic rst,

    input logic [SelectWidth-1:0] select,

    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0]            push_last,
    input  logic [NumFlows-1:0][Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid_unstable,
    output logic             pop_last_unstable,
    output logic [Width-1:0] pop_data_unstable
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_must_be_at_least_one_a, NumFlows >= 1)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)
  `BR_ASSERT_STATIC(select_only_stable_if_valid_stable_a,
                    EnableAssertPushValidStability || !EnableAssertSelectStability)
  `BR_ASSERT_INTG(select_in_range_a, select < NumFlows)

  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload_unstable;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFlows),
      .Width(Width + 1),
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
      .data (push_payload)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  if (NumFlows == 1) begin : gen_single_flow
    assign push_ready = pop_ready;
    assign pop_payload_unstable = push_payload[0];

    `BR_UNUSED(select)
  end else begin : gen_multi_flow

    logic holding, holding_next;
    logic [SelectWidth-1:0] held_select;

    logic accept;
    logic [SelectWidth-1:0] active_select;

    assign active_select = holding ? held_select : select;

    // Lint waivers are safe because we assert select is always in range.
    // ri lint_check_waive VAR_SHIFT TRUNC_LSHIFT
    assign push_ready = pop_ready << active_select;
    // ri lint_check_waive VAR_INDEX_READ
    assign pop_payload_unstable = push_payload[active_select];
    // ri lint_check_waive VAR_INDEX_READ
    assign pop_valid_unstable = push_valid[active_select];

    assign accept = pop_ready && pop_valid_unstable;
    assign holding_next = accept ? !push_last[active_select] : holding;

    `BR_REGI(holding, holding_next, 1'b0)
    `BR_REGLN(held_select, active_select, accept)

    if (EnableCoverPushBackpressure && EnableAssertPushValidStability) begin : gen_select_checks
      if (EnableAssertSelectStability) begin : gen_stable_select
        `BR_ASSERT_INTG(select_stable_a,
                        !holding && push_valid[select] && !push_ready[select] |=> $stable(select))
      end else begin : gen_unstable_select
        `BR_COVER_INTG(select_unstable_c,
                       !holding && push_valid[select] && !push_ready[select] ##1 !$stable(select))
      end
    end
  end

  if (NumFlows == 1) begin : gen_single_flow_outputs
    assign pop_valid_unstable = push_valid[0];
  end

  assign {pop_last_unstable, pop_data_unstable} = {
    pop_valid_unstable & pop_payload_unstable[Width], pop_payload_unstable[Width-1:0]
  };

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  localparam bit EnableAssertPopValidStability =
      EnableAssertPushValidStability && EnableAssertSelectStability;
  localparam bit EnableAssertPopDataStability =
      EnableAssertPopValidStability && EnableAssertPushDataStability;

  br_flow_checks_valid_data_impl #(
      .NumFlows(1),
      .Width(Width + 1),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPopValidStability),
      .EnableAssertDataStability(EnableAssertPopDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_impl (
      .clk,
      .rst,
      .ready(pop_ready),
      .valid(pop_valid_unstable),
      .data ({pop_last_unstable, pop_data_unstable})
  );

endmodule : br_flow_burst_mux_select_unstable
