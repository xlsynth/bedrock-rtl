// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Flow-Controlled Burst Multiplexer (Fixed-Priority)

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_burst_mux_fixed_fpv_monitor #(
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
    input logic [NumFlows-1:0]            push_last,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid_unstable,
    input logic                           pop_last_unstable,
    input logic [   Width-1:0]            pop_data_unstable,
    // RTL internal signal
    input logic [NumFlows-1:0]            grant
);

  localparam int IndexWidth = NumFlows == 1 ? 1 : $clog2(NumFlows);

  logic [NumFlows-1:0][Width:0] push_payload;
  logic [Width:0] pop_payload_unstable;
  for (genvar i = 0; i < NumFlows; i++) begin : gen_push_payload
    assign push_payload[i] = {push_last[i], push_data[i]};
  end
  assign pop_payload_unstable = {pop_last_unstable, pop_data_unstable};

  // ----------Instantiate basic checks----------
  br_flow_mux_basic_fpv_monitor #(
      .NumFlows(NumFlows),
      .Width(Width + 1),
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
      .push_data(push_payload),
      .pop_ready,
      .pop_valid(pop_valid_unstable),
      .pop_data (pop_payload_unstable)
  );

  // ----------Payload integrity checks----------
  logic [IndexWidth-1:0] index;
  `BR_FV_IDX(index, grant, NumFlows)
  `BR_ASSERT(grant_payload_integrity_a,
             pop_valid_unstable |-> pop_payload_unstable == push_payload[index])

endmodule : br_flow_burst_mux_fixed_fpv_monitor

bind br_flow_burst_mux_fixed br_flow_burst_mux_fixed_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
