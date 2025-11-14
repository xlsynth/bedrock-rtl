// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Stable Multiplexer (Fixed-Priority) FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_fixed_stable_fpv_monitor #(
    parameter int NumFlows = 1,  // Must be at least 1
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
    input logic [   Width-1:0]            pop_data
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

  // ----------FV Modeling Code----------
  logic [$clog2(NumFlows)-1:0] i, j;
  if (NumFlows > 1) begin : gen_ij
    `BR_FV_2RAND_IDX(i, j, NumFlows)
  end else begin : gen_i
    assign i = '0;
  end

  // ----------Fairness Check----------
  if (NumFlows > 1) begin : gen_multi_req
    if (EnableCoverPushBackpressure) begin : gen_fairness_checks
      `BR_ASSERT(strict_priority_a,
                 (i < j) && push_valid[i] && push_valid[j] |=> (pop_data == $past(
                     push_data[i]
                 )) || !$past(
                     pop_ready
                 ) || !$past(
                     push_ready[i]
                 ))
    end else begin : gen_no_conflict_checks
      `BR_ASSERT(no_conflict_a, (i != j) |-> !(push_valid[i] && push_valid[j]))
    end
  end

endmodule : br_flow_mux_fixed_stable_fpv_monitor

bind br_flow_mux_fixed_stable br_flow_mux_fixed_stable_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .RegisterPopReady(RegisterPopReady),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
