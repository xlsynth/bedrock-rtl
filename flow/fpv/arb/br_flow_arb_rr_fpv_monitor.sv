// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Arbiter (Round Robin) FPV monitor

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_arb_rr_fpv_monitor #(
    parameter int NumFlows = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic                clk,
    input logic                rst,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic                pop_ready,
    input logic                pop_valid_unstable,
    // RTL internal signal
    input logic [NumFlows-1:0] grant
);

  // ----------Instantiate basic checks----------
  br_flow_arb_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability)
  ) fv_checker (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .pop_ready,
      .pop_valid_unstable
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

endmodule : br_flow_arb_rr_fpv_monitor

bind br_flow_arb_rr br_flow_arb_rr_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
