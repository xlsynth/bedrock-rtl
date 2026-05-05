// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Burst Multiplexer Core
//
// Wraps an external arbiter with grant-hold behavior to keep the selected
// requester granted until it asserts push_last alongside push_valid.
// push_last is muxed alongside push_data so the wrapped mux core handles the
// full burst payload.

`include "br_asserts.svh"

module br_flow_burst_mux_core #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    // If 1, cover that the push side experiences backpressure.
    // If 0, disable backpressure coverage. By default, this also
    // asserts that backpressure is impossible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
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
    output logic                           pop_valid_unstable,
    output logic                           pop_last_unstable,
    output logic [   Width-1:0]            pop_data_unstable
);

  localparam int PayloadWidth = Width + 1;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(legal_assert_no_push_backpressure_a,
                    !(EnableAssertNoPushBackpressure && EnableCoverPushBackpressure))
  `BR_ASSERT_STATIC(num_flows_gte_1_a, NumFlows >= 1)
  `BR_ASSERT_STATIC(datawidth_gte_1_a, Width >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [NumFlows-1:0] grant;
  logic [NumFlows-1:0] grant_hold;
  logic enable_priority_update_from_mux;
  logic enable_grant_hold_update;
  logic [NumFlows-1:0][PayloadWidth-1:0] push_payload;
  logic [PayloadWidth-1:0] pop_payload_unstable;

  assign grant_hold = ~(push_valid & push_last);
  assign enable_grant_hold_update = enable_priority_update_from_mux && |(grant & push_valid);

  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end

  br_arb_grant_hold #(
      .NumRequesters(NumFlows)
  ) br_arb_grant_hold (
      .clk,
      .rst,
      .grant_hold,
      .enable_grant_hold_update,
      .grant_from_arb,
      .enable_priority_update_to_arb(enable_priority_update),
      .grant
  );

  br_flow_mux_core #(
      .NumFlows(NumFlows),
      .Width(PayloadWidth),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .ArbiterAlwaysGrants(0)
  ) br_flow_mux_core (
      .clk,
      .rst,
      .request,
      .can_grant(grant),
      .grant,
      .enable_priority_update(enable_priority_update_from_mux),
      .push_ready,
      .push_valid,
      .push_data(push_payload),
      .pop_ready,
      .pop_valid_unstable,
      .pop_data_unstable(pop_payload_unstable)
  );

  assign {pop_last_unstable, pop_data_unstable} = pop_payload_unstable;

endmodule : br_flow_burst_mux_core
