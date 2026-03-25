// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Burst Multiplexer (Least-Recently-Used)

`include "br_asserts.svh"

module br_flow_burst_mux_lru_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                           clk,
    input logic                           rst,
    input logic [NumFlows-1:0]            push_ready,
    input logic [NumFlows-1:0]            push_valid,
    input logic [NumFlows-1:0]            push_last,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid_unstable,
    input logic                           pop_last_unstable,
    input logic [   Width-1:0]            pop_data_unstable,
    // RTL internal signals
    input logic [NumFlows-1:0]            grant,
    input logic [NumFlows-1:0]            grant_from_arb,
    input logic                           enable_priority_update
);

  // ----------Instantiate basic checks----------
  br_flow_burst_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPopDataStability(0)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_last,
      .push_data,
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_last (pop_last_unstable),
      .pop_data (pop_data_unstable)
  );

  // ----------LRU checks----------
  lru_basic_fpv_monitor #(
      .NumRequesters(NumFlows),
      .EnableCoverRequestMultihot(EnableCoverPushBackpressure)
  ) lru_check (
      .clk,
      .rst,
      .enable_priority_update,
      .request(push_valid),
      .grant  (grant_from_arb)
  );

endmodule : br_flow_burst_mux_lru_fpv_monitor

bind br_flow_burst_mux_lru br_flow_burst_mux_lru_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (
    .*,
    .grant(br_flow_burst_mux_core.grant)
);
