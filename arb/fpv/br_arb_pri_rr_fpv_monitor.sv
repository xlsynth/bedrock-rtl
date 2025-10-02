// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Prioritized Round Robin Arbiter FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_arb_pri_rr_fpv_monitor #(
    // Must be at least 2
    parameter int NumRequesters = 2,
    // Must be at least 2
    parameter int NumPriorities = 2
) (
    input logic clk,
    input logic rst,
    input logic enable_priority_update,
    input logic [NumRequesters-1:0] request,
    input logic [NumRequesters-1:0][$clog2(NumPriorities)-1:0] request_priority,
    input logic [NumRequesters-1:0] grant
);

  // ----------FV Modeling Code----------
  logic [$clog2(NumPriorities)-1:0] max_priority;
  logic [NumRequesters-1:0] highest_priority_request;

  always_comb begin
    max_priority = '0;
    for (int n = 0; n < NumRequesters; n++) begin
      if (request[n] && (request_priority[n] > max_priority)) begin
        max_priority = request_priority[n];
      end
    end
  end

  always_comb begin
    for (int n = 0; n < NumRequesters; n++) begin
      highest_priority_request[n] = request[n] && (request_priority[n] == max_priority);
    end
  end

  // ----------FV assumptions----------
  for (genvar i = 0; i < NumRequesters; i++) begin : gen_asm
    `BR_ASSUME(req_priority_range_a, request[i] |-> request_priority[i] < NumPriorities)
  end

  // ----------Instantiate arb_rr FV checker----------
  br_arb_rr_fpv_monitor #(
      .NumRequesters(NumRequesters)
  ) br_arb_rr_fpv_monitor (
      .clk,
      .rst,
      .enable_priority_update,
      .request(highest_priority_request),
      .grant  (grant)
  );

endmodule : br_arb_pri_rr_fpv_monitor

bind br_arb_pri_rr br_arb_pri_rr_fpv_monitor #(
    .NumRequesters(NumRequesters),
    .NumPriorities(NumPriorities)
) monitor (.*);
