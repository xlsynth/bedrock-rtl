// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Demux with Select (Unstable)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_demux_select_unstable_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
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
    input logic                                   push_ready,
    input logic                                   push_valid,
    input logic [           Width-1:0]            push_data,
    input logic [        NumFlows-1:0]            pop_ready,
    input logic [        NumFlows-1:0]            pop_valid_unstable,
    input logic [        NumFlows-1:0][Width-1:0] pop_data_unstable
);

  // ----------Instantiate basic checks----------
  br_flow_demux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertSelectStability(EnableAssertSelectStability),
      .EnableAssertPopValidStability(EnableAssertPushValidStability && EnableAssertSelectStability),
      .EnableAssertPopDataStability(EnableAssertPushDataStability && EnableAssertSelectStability)
  ) fv_checker (
      .clk,
      .rst,
      .select,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_data (pop_data_unstable)
  );

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  // ----------select check----------
  `BR_ASSERT(select_data_check_a,
             pop_valid_unstable[select] |-> pop_data_unstable[select] == push_data)
  `BR_ASSERT(forward_progress_a, push_valid |-> pop_valid_unstable[select])

endmodule : br_flow_demux_select_unstable_fpv_monitor

bind br_flow_demux_select_unstable br_flow_demux_select_unstable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
