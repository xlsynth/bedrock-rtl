// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Superintelligent CSR Bus CDC
//
// This module provides CDC for the Superintelligent CSR Bus.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_csr_cdc #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be either 32 or 64
    // If 1 (the default), register upstream_rst on push_clk and downstream_rst on downstream_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless upstream_rst and downstream_rst are driven directly by
    // registers.
    parameter bit RegisterResetActive = 1,
    // If 1, register the downstream request outputs on downstream_clk.
    // If 0, downstream request outputs will be an asynchronous path from upstream_clk.
    parameter bit RegisterDownstreamReqOutputs = 0,
    // If 1, register the upstream response outputs on upstream_clk.
    // If 0, upstream response outputs will be an asynchronous path from downstream_clk.
    parameter bit RegisterUpstreamRespOutputs = 0,
    // If 1, add an additional register on the downstream abort signal
    parameter bit RegisterDownstreamAbort = 0,
    // Number of synchronization stages. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumSyncStages = 3,

    localparam int StrobeWidth = DataWidth / 8
) (
    input logic upstream_clk,
    input logic upstream_rst,
    input logic upstream_req_valid,
    input logic upstream_req_write,
    input logic [AddrWidth-1:0] upstream_req_addr,
    input logic [DataWidth-1:0] upstream_req_wdata,
    input logic [StrobeWidth-1:0] upstream_req_wstrb,
    input logic upstream_req_secure,
    input logic upstream_req_privileged,
    input logic upstream_req_abort,
    output logic upstream_resp_valid,
    output logic [DataWidth-1:0] upstream_resp_rdata,
    output logic upstream_resp_slverr,
    output logic upstream_resp_decerr,

    input logic downstream_clk,
    input logic downstream_rst,
    output logic downstream_req_valid,
    output logic downstream_req_write,
    output logic [AddrWidth-1:0] downstream_req_addr,
    output logic [DataWidth-1:0] downstream_req_wdata,
    output logic [StrobeWidth-1:0] downstream_req_wstrb,
    output logic downstream_req_secure,
    output logic downstream_req_privileged,
    output logic downstream_req_abort,
    input logic downstream_resp_valid,
    input logic [DataWidth-1:0] downstream_resp_rdata,
    input logic downstream_resp_slverr,
    input logic downstream_resp_decerr
);
  // Integration assertions
  // Rely on checks in submodules.

  // Implementation

  // Request CDC
  typedef struct packed {
    logic write;
    logic [AddrWidth-1:0] addr;
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic secure;
    logic privileged;
  } req_t;

  logic upstream_req_ready;
  req_t upstream_req;
  req_t downstream_req;

  assign upstream_req = '{
          write: upstream_req_write,
          addr: upstream_req_addr,
          wdata: upstream_req_wdata,
          wstrb: upstream_req_wstrb,
          secure: upstream_req_secure,
          privileged: upstream_req_privileged
      };

  br_cdc_reg #(
      .Width($bits(req_t)),
      .RegisterResetActive(RegisterResetActive),
      .RegisterPopOutputs(RegisterDownstreamReqOutputs),
      .NumSyncStages(NumSyncStages)
  ) br_cdc_reg_req (
      .push_clk(upstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .push_rst(upstream_rst),
      .push_ready(upstream_req_ready),
      .push_valid(upstream_req_valid),
      .push_data(upstream_req),
      .pop_clk(downstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .pop_rst(downstream_rst),
      .pop_ready(1'b1),
      .pop_valid(downstream_req_valid),
      .pop_data(downstream_req)
  );

  assign downstream_req_write = downstream_req.write;
  assign downstream_req_addr = downstream_req.addr;
  assign downstream_req_wdata = downstream_req.wdata;
  assign downstream_req_wstrb = downstream_req.wstrb;
  assign downstream_req_secure = downstream_req.secure;
  assign downstream_req_privileged = downstream_req.privileged;

  // Response CDC
  typedef struct packed {
    logic [DataWidth-1:0] rdata;
    logic slverr;
    logic decerr;
  } resp_t;

  logic  downstream_resp_ready;
  resp_t downstream_resp;
  resp_t upstream_resp;

  assign downstream_resp = '{
          rdata: downstream_resp_rdata,
          slverr: downstream_resp_slverr,
          decerr: downstream_resp_decerr
      };

  br_cdc_reg #(
      .Width($bits(resp_t)),
      .RegisterResetActive(RegisterResetActive),
      .RegisterPopOutputs(RegisterUpstreamRespOutputs),
      .NumSyncStages(NumSyncStages)
  ) br_cdc_reg_resp (
      .push_clk(downstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .push_rst(downstream_rst),
      .push_ready(downstream_resp_ready),
      .push_valid(downstream_resp_valid),
      .push_data(downstream_resp),
      .pop_clk(upstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .pop_rst(upstream_rst),
      .pop_ready(1'b1),
      .pop_valid(upstream_resp_valid),
      .pop_data(upstream_resp)
  );

  assign upstream_resp_rdata  = upstream_resp.rdata;
  assign upstream_resp_slverr = upstream_resp.slverr;
  assign upstream_resp_decerr = upstream_resp.decerr;

  // Abort CDC
  br_cdc_bit_pulse #(
      .NumStages(NumSyncStages),
      .RegisterOutput(RegisterDownstreamAbort)
  ) br_cdc_bit_pulse_abort (
      .src_clk(upstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(upstream_rst),
      .src_pulse(upstream_req_abort),
      .dst_clk(downstream_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(downstream_rst),
      .dst_pulse(downstream_req_abort)
  );

  // Only used for assertions.
  `BR_UNUSED(upstream_req_ready)
  `BR_UNUSED(downstream_resp_ready)

  // Implementation assertions
  `BR_ASSERT_CR_IMPL(no_req_backpressure_a, upstream_req_valid |-> upstream_req_ready,
                     upstream_clk, upstream_rst)
  `BR_ASSERT_CR_IMPL(no_resp_backpressure_a, downstream_resp_valid |-> downstream_resp_ready,
                     downstream_clk, downstream_rst)

endmodule : br_csr_cdc
