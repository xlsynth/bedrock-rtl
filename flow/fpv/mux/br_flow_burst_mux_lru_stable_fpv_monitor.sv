// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Stable Burst Multiplexer (Least-Recently-Used)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_burst_mux_lru_stable_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit RegisterPopReady = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int IndexWidth = NumFlows == 1 ? 1 : $clog2(NumFlows),
    localparam int MaxPending = NumFlows == 1 ? 2 : NumFlows
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

  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload;
  logic [NumFlows-1:0] push_handshake;
  logic [IndexWidth-1:0] index;

  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end
  assign pop_payload = {pop_last, pop_data};
  assign push_handshake = push_valid & push_ready;
  `BR_FV_IDX(index, push_handshake, NumFlows)

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width + 1),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(1),
      .EnableAssertPopValidStability(1),
      .EnableAssertPopDataStability(1),
      .DelayedGrant(1)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data(push_payload),
      .pop_ready,
      .pop_valid,
      .pop_data (pop_payload)
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
      .grant
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width + 1),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPending)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(|push_handshake),
      .incoming_data(push_payload[index]),
      .outgoing_vld(pop_valid & pop_ready),
      .outgoing_data(pop_payload)
  );

endmodule : br_flow_burst_mux_lru_stable_fpv_monitor

bind br_flow_burst_mux_lru_stable br_flow_burst_mux_lru_stable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .RegisterPopReady(RegisterPopReady),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
