// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Mux with Select
//
// A dataflow pipeline mux with explicit binary select.
// Uses the AMBA-inspired ready-valid handshake protocol
// for synchronizing pipeline stages and stalling when
// encountering backpressure hazards.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.

`include "br_registers.svh"

module br_flow_mux_select #(
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
    // If 1, assert that select will not change when the selected push flow is backpressured.
    // Otherwise, cover that select can be unstable.
    parameter bit EnableAssertSelectStability = 0,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,  // Synchronous active-high

    input logic [$clog2(NumFlows)-1:0] select,

    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0][Width-1:0] push_data,

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Register the pop outputs to hide the delays of the combinational muxing logic.
  // Note that there are still combinational paths from pop_ready and select to push_ready.

  logic internal_ready;
  logic internal_valid_unstable;
  logic [Width-1:0] internal_data_unstable;

  br_flow_mux_select_unstable #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertSelectStability(EnableAssertSelectStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_mux_select_unstable (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready         (internal_ready),
      .pop_valid_unstable(internal_valid_unstable),
      .pop_data_unstable (internal_data_unstable)
  );

  // internal_valid could be unstable if push_valid or select is unstable.
  localparam bit EnableAssertInternalValidStability =
      EnableAssertPushValidStability && EnableAssertSelectStability;
  localparam bit EnableAssertInternalDataStability =
      EnableAssertInternalValidStability && EnableAssertPushDataStability;

  br_flow_reg_fwd #(
      .Width(Width),
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
      .push_data (internal_data_unstable),
      .pop_ready,
      .pop_valid,
      .pop_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_flow_mux_select
