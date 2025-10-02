// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Multiplexer (Round-Robin)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_flow_mux_select_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                                   clk,
    input logic                                   rst,
    input logic [$clog2(NumFlows)-1:0]            select,
    input logic [        NumFlows-1:0]            push_ready,
    input logic [        NumFlows-1:0]            push_valid,
    input logic [        NumFlows-1:0][Width-1:0] push_data,
    input logic                                   pop_ready,
    input logic                                   pop_valid,
    input logic [           Width-1:0]            pop_data
);

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      // Final flow mux stage ensures output is always stable
      .EnableAssertPopValidStability(1),
      .EnableAssertPopDataStability(1),
      .EnableAssertMustGrant(0)
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

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  if (EnableAssertSelectStability) begin : gen_stable_select
    `BR_ASSUME(select_stable_a, push_valid[select] && !push_ready[select] |=> $stable(select))
  end

  // ----------select check----------
  logic [Width-1:0] fv_data;
  `BR_REGLN(fv_data, push_data[select], push_valid[select] & push_ready[select])

  `BR_ASSERT(select_data_check_a, pop_valid |-> pop_data == fv_data)
  // select can pick invalid index
  `BR_ASSERT(forward_progress_a, push_valid[select] |=> pop_valid)

endmodule : br_flow_mux_select_fpv_monitor

bind br_flow_mux_select br_flow_mux_select_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
