// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Crossbar (Fixed Priority Arbitration) FPV checker

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_xbar_fixed_fpv_monitor #(
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
    input logic [NumPopFlows-1:0][NumPushFlows-1:0] grant
);

  // ----------FV Modeling Code----------
  logic [$clog2(NumPushFlows)-1:0] i, j;
  logic push_valid_i;
  logic push_valid_j;
  // pick a random pair of input/outout flow to check
  logic [DestIdWidth-1:0] fv_push_id;
  logic [DestIdWidth-1:0] fv_pop_id;
  `BR_ASSUME(fv_push_id_stable_a, $stable(fv_push_id) && fv_push_id < NumPushFlows)
  `BR_ASSUME(fv_pop_id_stable_a, $stable(fv_pop_id) && fv_pop_id < NumPopFlows)

  if (NumPushFlows > 1) begin : gen_ij
    `BR_FV_2RAND_IDX(i, j, NumPushFlows)
  end else begin : gen_ij0
    assign i = 0;
    assign j = 0;
  end

  assign push_valid_i = push_valid[i] && (push_dest_id[i] == fv_pop_id);
  assign push_valid_j = push_valid[j] && (push_dest_id[j] == fv_pop_id);

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

  // ----------FV assertions----------
  if (NumPushFlows > 1) begin : gen_multiple_req
    if (EnableCoverPushBackpressure) begin : gen_priority_checks
      if (RegisterDemuxOutputs) begin : gen_lat
        `BR_ASSERT(strict_priority_a,
                   (i < j) && push_valid_i && push_valid_j |=> !grant[fv_pop_id][j])
      end else begin : gen_lat0
        `BR_ASSERT(strict_priority_a,
                   (i < j) && push_valid_i && push_valid_j |-> !grant[fv_pop_id][j])
      end
    end else begin : gen_check_no_conflict
      `BR_ASSERT(no_conflict_a, !(push_valid_i && push_valid_j))
    end
  end

endmodule : br_flow_xbar_fixed_fpv_monitor

bind br_flow_xbar_fixed br_flow_xbar_fixed_fpv_monitor #(
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
