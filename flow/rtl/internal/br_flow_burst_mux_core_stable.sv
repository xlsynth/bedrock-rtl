// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Stable Burst Multiplexer Core
//
// Wraps an external arbiter with grant-hold behavior to keep the selected
// requester granted until it asserts push_last alongside push_valid.
// push_last is muxed alongside push_data so the wrapped mux core handles the
// full burst payload.
//
// Adds a flow register to the output to ensure that pop_valid/pop_last/
// pop_data are stable.

`include "br_asserts.svh"

module br_flow_burst_mux_core_stable #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    // If 1, ensure that the pop ready signal is registered
    // at the input. This ensures there is no combinational path
    // from pop_ready to push_ready.
    parameter bit RegisterPopReady = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1
) (
    input  logic                           clk,
    input  logic                           rst,
    // Interface to base arbiter
    output logic [NumFlows-1:0]            request,
    input  logic [NumFlows-1:0]            grant_from_arb,
    output logic                           enable_priority_update,
    // External-facing signals
    output logic [NumFlows-1:0]            push_ready,
    input  logic [NumFlows-1:0]            push_valid,
    input  logic [NumFlows-1:0]            push_last,
    input  logic [NumFlows-1:0][Width-1:0] push_data,
    input  logic                           pop_ready,
    output logic                           pop_valid,
    output logic                           pop_last,
    output logic [   Width-1:0]            pop_data
);

  localparam int PayloadWidth = Width + 1;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(num_flows_gte_1_a, NumFlows >= 1)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic internal_pop_ready;
  logic internal_pop_valid_unstable;
  logic internal_pop_last_unstable;
  logic [Width-1:0] internal_pop_data_unstable;
  logic [PayloadWidth-1:0] internal_pop_payload_unstable;
  logic [PayloadWidth-1:0] pop_payload;

  assign internal_pop_payload_unstable = {internal_pop_last_unstable, internal_pop_data_unstable};

  br_flow_burst_mux_core #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_burst_mux_core (
      .clk,
      .rst,
      .request,
      .grant_from_arb,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready(internal_pop_ready),
      .pop_valid_unstable(internal_pop_valid_unstable),
      .pop_last_unstable(internal_pop_last_unstable),
      .pop_data_unstable(internal_pop_data_unstable)
  );

  if (RegisterPopReady) begin : gen_flow_reg_both
    br_flow_reg_both #(
        .Width(PayloadWidth),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        // internal_pop_payload_unstable cannot be stable
        .EnableAssertPushDataStability(0),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_both (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid_unstable),
        .push_data (internal_pop_payload_unstable),
        .pop_ready,
        .pop_valid,
        .pop_data  (pop_payload)
    );
  end else begin : gen_flow_reg_fwd
    br_flow_reg_fwd #(
        .Width(PayloadWidth),
        .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
        .EnableAssertPushValidStability(EnableAssertPushValidStability),
        // internal_pop_payload_unstable cannot be stable
        .EnableAssertPushDataStability(0),
        .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_ready(internal_pop_ready),
        .push_valid(internal_pop_valid_unstable),
        .push_data (internal_pop_payload_unstable),
        .pop_ready,
        .pop_valid,
        .pop_data  (pop_payload)
    );
  end

  assign {pop_last, pop_data} = pop_payload;

endmodule : br_flow_burst_mux_core_stable
