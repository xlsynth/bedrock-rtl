// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_rr_stable_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    parameter bit RegisterPopReady = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                           clk,
    input logic                           rst,
    input logic [NumFlows-1:0]            push_ready,
    input logic [NumFlows-1:0]            push_valid,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid,
    input logic [   Width-1:0]            pop_data,
    // RTL internal signal
    input logic [NumFlows-1:0]            grant,
    input logic                           enable_priority_update
);

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
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
      .push_data,
      .pop_ready,
      .pop_valid,
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
      .request(push_valid),
      .grant
  );

  // ----------Data integrity Check----------
  logic [$clog2(NumFlows)-1:0] index;
  `BR_FV_IDX(index, grant, NumFlows)

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumFlows)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid[index] & push_ready[index]),
      .incoming_data(push_data[index]),
      .outgoing_vld(pop_valid & pop_ready),
      .outgoing_data(pop_data)
  );

endmodule : br_flow_mux_rr_stable_fpv_monitor

bind br_flow_mux_rr_stable br_flow_mux_rr_stable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .RegisterPopReady(RegisterPopReady),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
