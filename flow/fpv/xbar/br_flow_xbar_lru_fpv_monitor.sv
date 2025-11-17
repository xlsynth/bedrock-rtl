// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Crossbar (Least-Recently Used Arbitration) FPV checker

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_xbar_lru_fpv_monitor #(
    // The number of input flows. Must be >=2.
    parameter int NumPushFlows = 2,
    // The number of output flows. Must be >=2.
    parameter int NumPopFlows = 2,
    // The width of the data bus.
    parameter int Width = 1,
    // If 1, registers are inserted between the demux and mux to break up the
    // timing path, increasing the cut-through latency by 1. Note that this
    // results in NumPushFlows x NumPopFlows x Width bits of registers being
    // inserted.
    parameter bit RegisterDemuxOutputs = 0,
    // If 1, registers are inserted at the output of the muxes, ensuring that
    // pop_valid/pop_data come directly from registers.
    // If 0, pop_valid/pop_data come directly from the muxes and may be unstable.
    parameter bit RegisterPopOutputs = 0,
    // If 1, cover that the push_ready signal can be backpressured.
    // If 0, assert that push backpressure is not possible.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assume that push_valid is stable.
    parameter bit EnableAssumePushValidStability = EnableCoverPushBackpressure,
    // If 1, assume that push_data is stable.
    parameter bit EnableAssumePushDataStability = EnableAssumePushValidStability,
    // If 1, assume that push_dest_id is stable.
    parameter bit EnableAssumePushDestinationStability = EnableAssumePushValidStability,
    // If 1, assert that push_valid is 1 and all intermediate
    // register stages are empty at end of simulation.
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int DestIdWidth = $clog2(NumPopFlows)
) (
    input logic clk,
    input logic rst,

    input logic [NumPushFlows-1:0] push_ready,
    input logic [NumPushFlows-1:0] push_valid,
    input logic [NumPushFlows-1:0][Width-1:0] push_data,
    input logic [NumPushFlows-1:0][DestIdWidth-1:0] push_dest_id,

    input logic [NumPopFlows-1:0] pop_ready,
    input logic [NumPopFlows-1:0] pop_valid,
    input logic [NumPopFlows-1:0][Width-1:0] pop_data,

    // RTL internal signals
    input logic [NumPopFlows-1:0][NumPushFlows-1:0] request,
    input logic [NumPopFlows-1:0][NumPushFlows-1:0] grant,
    input logic [NumPopFlows-1:0] enable_priority_update
);

  // ----------FV Modeling Code----------
  localparam int PushDestIdWidth = $clog2(NumPushFlows);
  // pick a random pair of input/outout flow to check
  logic [PushDestIdWidth-1:0] fv_push_id;
  logic [DestIdWidth-1:0] fv_pop_id;
  `BR_ASSUME(fv_push_id_stable_a, $stable(fv_push_id) && fv_push_id < NumPushFlows)
  `BR_ASSUME(fv_pop_id_stable_a, $stable(fv_pop_id) && fv_pop_id < NumPopFlows)

  // ----------Instantiate basic checks----------
  br_flow_xbar_basic_fpv_monitor #(
      .NumPushFlows(NumPushFlows),
      .NumPopFlows(NumPopFlows),
      .Width(Width),
      .RegisterDemuxOutputs(RegisterDemuxOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssumePushValidStability(EnableAssumePushValidStability),
      .EnableAssumePushDataStability(EnableAssumePushDataStability),
      .EnableAssumePushDestinationStability(EnableAssumePushDestinationStability)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .push_dest_id,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .fv_push_id,
      .fv_pop_id
  );

  // ----------LRU checks----------
  lru_basic_fpv_monitor #(
      .NumRequesters(NumPushFlows),
      .EnableCoverRequestMultihot(EnableCoverPushBackpressure)
  ) lru_check (
      .clk,
      .rst,
      .enable_priority_update(enable_priority_update[fv_pop_id]),
      .request(request[fv_pop_id]),
      .grant(grant[fv_pop_id])
  );

endmodule : br_flow_xbar_lru_fpv_monitor

bind br_flow_xbar_lru br_flow_xbar_lru_fpv_monitor #(
    .NumPushFlows(NumPushFlows),
    .NumPopFlows(NumPopFlows),
    .Width(Width),
    .RegisterDemuxOutputs(RegisterDemuxOutputs),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
