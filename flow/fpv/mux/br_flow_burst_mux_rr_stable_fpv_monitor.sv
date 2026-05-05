// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Stable Burst Multiplexer (Round-Robin)

module br_flow_burst_mux_rr_stable_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit RegisterPopReady = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic                           clk,
    input logic                           rst,
    input logic [NumFlows-1:0]            push_ready,
    input logic [NumFlows-1:0]            push_valid,
    input logic [NumFlows-1:0]            push_last,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid,
    input logic                           pop_last,
    input logic [   Width-1:0]            pop_data,
    // RTL internal signals
    input logic [NumFlows-1:0]            grant,
    input logic                           enable_priority_update
);
  // ----------Instantiate basic checks----------
  br_flow_burst_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(1),
      .EnableAssertPopValidStability(1),
      .EnableAssertPopDataStability(1)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_last,
      .pop_data
  );

  // ----------Round Robin checks----------
  rr_basic_fpv_monitor #(
      .NumRequesters(NumFlows),
      .EnableAssertPushValidStability(EnableAssertPushValidStability)
  ) rr_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request(push_valid & push_ready),
      .grant
  );
endmodule : br_flow_burst_mux_rr_stable_fpv_monitor

bind br_flow_burst_mux_rr_stable br_flow_burst_mux_rr_stable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .RegisterPopReady(RegisterPopReady),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (
    .*,
    .grant(br_flow_burst_mux_core_stable.br_flow_burst_mux_core.grant)
);
