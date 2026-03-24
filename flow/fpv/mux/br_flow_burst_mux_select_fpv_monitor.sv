// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow Burst Mux with Select

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_flow_burst_mux_select_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int IndexWidth = NumFlows == 1 ? 1 : $clog2(NumFlows)
) (
    input logic                             clk,
    input logic                             rst,
    input logic [IndexWidth-1:0]            select,
    input logic [  NumFlows-1:0]            push_ready,
    input logic [  NumFlows-1:0]            push_valid,
    input logic [  NumFlows-1:0]            push_last,
    input logic [  NumFlows-1:0][Width-1:0] push_data,
    input logic                             pop_ready,
    input logic                             pop_valid,
    input logic                             pop_last,
    input logic [     Width-1:0]            pop_data
);

  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload;
  logic [NumFlows-1:0] push_handshake;
  logic [IndexWidth-1:0] index;
  logic [Width:0] fv_payload;

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
      .EnableAssertMustGrant(0),
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

  // ----------FV assumptions----------
  `BR_ASSUME(select_range_a, select < NumFlows)

  `BR_REGLN(fv_payload, push_payload[index], |push_handshake)
  `BR_ASSERT(select_payload_check_a, pop_valid |-> pop_payload == fv_payload)

endmodule : br_flow_burst_mux_select_fpv_monitor

bind br_flow_burst_mux_select br_flow_burst_mux_select_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertSelectStability(EnableAssertSelectStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
