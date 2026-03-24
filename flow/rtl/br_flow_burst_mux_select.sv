// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Burst Mux with Select
//
// A dataflow pipeline mux with explicit binary select and burst ownership.
// Once a selected flow wins a non-terminal beat, that flow remains selected
// until it later presents push_last alongside push_valid.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.

module br_flow_burst_mux_select #(
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
    input logic clk,
    input logic rst,

    input logic [SelectWidth-1:0] select,

    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0]            push_last,
    input  logic [NumFlows-1:0][Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic             pop_last,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic internal_ready;
  logic internal_valid_unstable;
  logic internal_last_unstable;
  logic [Width-1:0] internal_data_unstable;
  logic [Width:0] internal_payload_unstable;
  logic [Width:0] pop_payload;

  br_flow_burst_mux_select_unstable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertSelectStability(EnableAssertSelectStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_burst_mux_select_unstable (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready         (internal_ready),
      .pop_valid_unstable(internal_valid_unstable),
      .pop_last_unstable (internal_last_unstable),
      .pop_data_unstable (internal_data_unstable)
  );

  assign internal_payload_unstable = {internal_last_unstable, internal_data_unstable};

  localparam bit EnableAssertInternalValidStability =
      EnableAssertPushValidStability && EnableAssertSelectStability;
  localparam bit EnableAssertInternalDataStability =
      EnableAssertInternalValidStability && EnableAssertPushDataStability;

  br_flow_reg_fwd #(
      .Width(Width + 1),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertInternalValidStability),
      .EnableAssertPushDataStability(EnableAssertInternalDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_reg_fwd (
      .clk,
      .rst,
      .push_ready(internal_ready),
      .push_valid(internal_valid_unstable),
      .push_data (internal_payload_unstable),
      .pop_ready,
      .pop_valid,
      .pop_data  (pop_payload)
  );

  assign {pop_last, pop_data} = pop_payload;

endmodule : br_flow_burst_mux_select
