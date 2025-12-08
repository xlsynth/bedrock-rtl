// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Multiplexer (Round-Robin)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_rr_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
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
    input logic [   Width-1:0]            pop_data_unstable,
    // RTL internal signal
    input logic [NumFlows-1:0]            grant
);

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableCoverPopBackpressure(EnableCoverPushBackpressure),
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

  // ----------Round Robin checks----------
  rr_basic_fpv_monitor #(
      .NumRequesters(NumFlows),
      .EnableAssertPushValidStability(EnableAssertPushValidStability)
  ) rr_check (
      .clk,
      .rst,
      .enable_priority_update(pop_ready),
      .request(push_valid),
      .grant
  );

  logic [$clog2(NumFlows)-1:0] index;
  `BR_FV_IDX(index, grant, NumFlows)
  `BR_ASSERT(grant_data_integrity_a, pop_valid_unstable |-> pop_data_unstable == push_data[index])

endmodule : br_flow_mux_rr_fpv_monitor

bind br_flow_mux_rr br_flow_mux_rr_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
