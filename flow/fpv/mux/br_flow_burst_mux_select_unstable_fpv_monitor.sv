// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Burst Mux with Select (Unstable)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_burst_mux_select_unstable_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int SelectWidth = NumFlows == 1 ? 1 : $clog2(NumFlows)
) (
    input logic                              clk,
    input logic                              rst,
    input logic [SelectWidth-1:0]            select,
    input logic [   NumFlows-1:0]            push_ready,
    input logic [   NumFlows-1:0]            push_valid,
    input logic [   NumFlows-1:0]            push_last,
    input logic [   NumFlows-1:0][Width-1:0] push_data,
    input logic                              pop_ready,
    input logic                              pop_valid_unstable,
    input logic                              pop_last_unstable,
    input logic [      Width-1:0]            pop_data_unstable,
    // RTL internal signals
    input logic                              holding,
    input logic [SelectWidth-1:0]            held_select
);

  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload_unstable;
  logic [SelectWidth-1:0] active_select;
  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end
  assign pop_payload_unstable = {pop_last_unstable, pop_data_unstable};
  assign active_select = holding ? held_select : select;

  localparam bit EnableAssertPopValidStability =
      EnableAssertPushValidStability && EnableAssertSelectStability;
  localparam bit EnableAssertPopDataStability =
      EnableAssertPopValidStability && EnableAssertPushDataStability;

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width + 1),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPopValidStability(EnableAssertPopValidStability),
      .EnableAssertPopDataStability(EnableAssertPopDataStability),
      .EnableAssertMustGrant(0)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data(push_payload),
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_data (pop_payload_unstable)
  );

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  if (EnableAssertSelectStability) begin : gen_stable_select
    `BR_ASSUME(select_stable_a,
               !holding && push_valid[select] && !push_ready[select] |=> $stable(select))
  end

  // ----------Select checks----------
  `BR_ASSERT(select_payload_check_a,
             pop_valid_unstable |-> pop_payload_unstable == push_payload[active_select])
  `BR_ASSERT(forward_progress_a, push_valid[active_select] |-> pop_valid_unstable)

endmodule : br_flow_burst_mux_select_unstable_fpv_monitor

bind br_flow_burst_mux_select_unstable br_flow_burst_mux_select_unstable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
