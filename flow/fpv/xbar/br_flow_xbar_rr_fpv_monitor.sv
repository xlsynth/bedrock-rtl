// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Crossbar (Round-Robin Arbitration) FPV checker

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_xbar_rr_fpv_monitor #(
    parameter int NumPushFlows = 1,
    parameter int NumPopFlows = 1,
    parameter int Width = 1,
    parameter bit RegisterDemuxOutputs = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPushDestinationStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int DestIdWidth = br_math::clamped_clog2(NumPopFlows)
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
  // pick a random pair of input/outout flow to check
  logic [DestIdWidth-1:0] fv_push_id;
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
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDestinationStability(EnableAssertPushDestinationStability)
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

  // ----------Round Robin checks----------
  rr_basic_fpv_monitor #(
      .NumRequesters(NumPushFlows),
      // Valid won't be stable at the arbiters if push_dest_id is unstable
      .EnableAssertPushValidStability(EnableAssertPushDestinationStability)
  ) rr_check (
      .clk,
      .rst,
      .enable_priority_update(enable_priority_update[fv_pop_id]),
      .request(request[fv_pop_id]),
      .grant(grant[fv_pop_id])
  );

endmodule : br_flow_xbar_rr_fpv_monitor

bind br_flow_xbar_rr br_flow_xbar_rr_fpv_monitor #(
    .NumPushFlows(NumPushFlows),
    .NumPopFlows(NumPopFlows),
    .Width(Width),
    .RegisterDemuxOutputs(RegisterDemuxOutputs),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertPushDestinationStability(EnableAssertPushDestinationStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
