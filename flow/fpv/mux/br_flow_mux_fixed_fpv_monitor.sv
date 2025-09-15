// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fixed-Priority Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_fixed_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
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
    input logic                           pop_valid_unstable,
    input logic [   Width-1:0]            pop_data_unstable
);

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(EnableCoverPushBackpressure),
      // Pop data can never be stable
      .EnableAssertPopDataStability(0)
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

  // ----------FV Modeling Code----------
  logic [$clog2(NumFlows)-1:0] i, j;
  `BR_FV_2RAND_IDX(i, j, NumFlows)

  // ----------Fairness Check----------
  // verilog_lint: waive-start line-length
  if (EnableCoverPushBackpressure) begin : gen_strict_priority_check
    `BR_ASSERT(strict_priority_a,
               (i < j) && push_valid[i] && push_valid[j] |-> (pop_data_unstable == push_data[i]) || !push_ready[i])
  end else begin : gen_no_conflict_check
    `BR_ASSERT(no_conflict_a, i != j |-> !(push_valid[i] && push_valid[j]))
  end
  // verilog_lint: waive-stop line-length

endmodule : br_flow_mux_fixed_fpv_monitor

bind br_flow_mux_fixed br_flow_mux_fixed_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
