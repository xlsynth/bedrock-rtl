// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Multiplexer (Round-Robin)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_select_unstable_fpv_monitor #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter int Width = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = 0,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                                   clk,
    input logic                                   rst,
    input logic [$clog2(NumFlows)-1:0]            select,
    input logic [        NumFlows-1:0]            push_ready,
    input logic [        NumFlows-1:0]            push_valid,
    input logic [        NumFlows-1:0][Width-1:0] push_data,
    input logic                                   pop_ready,
    input logic                                   pop_valid_unstable,
    input logic [           Width-1:0]            pop_data_unstable
);

  // ----------Instantiate basic checks----------
  localparam bit EnableAssertPopValidStability =
      EnableAssertPushValidStability && EnableAssertSelectStability;
  localparam bit EnableAssertPopDataStability =
      EnableAssertPopValidStability && EnableAssertPushDataStability;

  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPopValidStability(EnableAssertPopValidStability),
      .EnableAssertPopDataStability(EnableAssertPopDataStability),
      // Select can pick a flow that is not valid
      .EnableAssertMustGrant(0)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_data (pop_data_unstable)
  );

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  if (EnableAssertSelectStability) begin : gen_stable_select
    `BR_ASSUME(select_stable_a, push_valid[select] && !push_ready[select] |=> $stable(select))
  end

  // ----------select check----------
  `BR_ASSERT(select_data_check_a, pop_valid_unstable |-> pop_data_unstable == push_data[select])
  `BR_ASSERT(forward_progress_a, push_valid[select] |-> pop_valid_unstable)

endmodule : br_flow_mux_select_unstable_fpv_monitor

bind br_flow_mux_select_unstable br_flow_mux_select_unstable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
