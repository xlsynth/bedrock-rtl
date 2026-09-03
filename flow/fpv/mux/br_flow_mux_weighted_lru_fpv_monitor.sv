// SPDX-License-Identifier: Apache-2.0


// Weighted LRU flow-mux FPV wrapper.

module br_flow_mux_weighted_lru_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter int MaxWeight = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    localparam int WeightWidth = $clog2(MaxWeight + 1)
) (
    input logic clk,
    input logic rst,
    input logic [NumFlows-1:0][WeightWidth-1:0] cfg_weight,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic pop_ready,
    input logic pop_valid_unstable,
    input logic [Width-1:0] pop_data_unstable,
    input logic [NumFlows-1:0] grant
);

  br_flow_mux_weighted_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width),
      .MaxWeight(MaxWeight),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) weighted_check (
      .*
  );

  logic [NumFlows-1:0] eligible_request;
  if (NumFlows > 1) begin : gen_weighted_requests
    logic [NumFlows-1:0] weighted_request;
    // Use the DUT's existing eligibility bits without duplicating weight state.
    assign weighted_request = push_valid &
        br_flow_mux_weighted_lru.br_arb_weighted_lru_inst.gen_n_req.request_priority;
    assign eligible_request = (|weighted_request) ? weighted_request : push_valid;
  end else begin : gen_single_flow
    assign eligible_request = push_valid;
  end

  // Disabling contention coverage also asserts no waiting in the basic checker.
  // Select that mode only when the mux contract forbids backpressure.
  localparam bit EnableCoverContention =
      EnableCoverPushBackpressure || !EnableAssertNoPushBackpressure;
  lru_basic_fpv_monitor #(
      .NumRequesters(NumFlows),
      .EnableCoverRequestMultihot(EnableCoverContention)
  ) lru_check (
      .clk,
      .rst,
      .enable_priority_update(pop_ready),
      .request(eligible_request),
      .grant
  );

endmodule : br_flow_mux_weighted_lru_fpv_monitor

bind br_flow_mux_weighted_lru br_flow_mux_weighted_lru_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .MaxWeight(MaxWeight),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability)
) monitor (.*);
