// SPDX-License-Identifier: Apache-2.0


//  Bedrock-RTL Flow Register (Reverse Variant) FPV monitor

`include "br_asserts.svh"

module br_flow_reg_rev_fpv_monitor #(
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic             clk,
    input logic             rst,
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data
);

  // ----------Instantiate basic checks----------
  br_flow_reg_basic_fpv_monitor #(
      .Width(Width),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
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

  // ----------Forward Progress Check----------
  `BR_ASSERT(pop_valid_a, push_valid |-> pop_valid)
  `BR_ASSERT(push_ready_a, pop_ready |=> push_ready)

endmodule : br_flow_reg_rev_fpv_monitor

bind br_flow_reg_rev br_flow_reg_rev_fpv_monitor #(
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
