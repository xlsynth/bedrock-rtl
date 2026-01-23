// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL CSR CDC FPV Monitor

`include "br_asserts.svh"
module br_csr_cdc_fpv_monitor #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 32,
    parameter bit RegisterResetActive = 1,
    parameter bit RegisterDownstreamReqOutputs = 0,
    parameter bit RegisterUpstreamRespOutputs = 0,
    parameter bit RegisterDownstreamAbort = 0,
    parameter int NumSyncStages = 3,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

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

    input logic downstream_clk,
    input logic downstream_rst,
    input logic downstream_resp_valid,
    input logic [DataWidth-1:0] downstream_resp_rdata,
    input logic downstream_resp_slverr,
    input logic downstream_resp_decerr
);
  logic upstream_resp_valid;
  logic [DataWidth-1:0] upstream_resp_rdata;
  logic upstream_resp_slverr;
  logic upstream_resp_decerr;
  logic downstream_req_valid;
  logic downstream_req_write;
  logic [AddrWidth-1:0] downstream_req_addr;
  logic [DataWidth-1:0] downstream_req_wdata;
  logic [StrobeWidth-1:0] downstream_req_wstrb;
  logic downstream_req_secure;
  logic downstream_req_privileged;
  logic downstream_req_abort;

  // ----------Instantiate DUT----------
  br_csr_cdc #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .RegisterResetActive(RegisterResetActive),
      .RegisterDownstreamReqOutputs(RegisterDownstreamReqOutputs),
      .RegisterUpstreamRespOutputs(RegisterUpstreamRespOutputs),
      .RegisterDownstreamAbort(RegisterDownstreamAbort),
      .NumSyncStages(NumSyncStages)
  ) dut (
      .upstream_clk,
      .upstream_rst,
      .upstream_req_valid,
      .upstream_req_write,
      .upstream_req_addr,
      .upstream_req_wdata,
      .upstream_req_wstrb,
      .upstream_req_secure,
      .upstream_req_privileged,
      .upstream_req_abort,
      .upstream_resp_valid,
      .upstream_resp_rdata,
      .upstream_resp_slverr,
      .upstream_resp_decerr,
      .downstream_clk,
      .downstream_rst,
      .downstream_req_valid,
      .downstream_req_write,
      .downstream_req_addr,
      .downstream_req_wdata,
      .downstream_req_wstrb,
      .downstream_req_secure,
      .downstream_req_privileged,
      .downstream_req_abort,
      .downstream_resp_valid,
      .downstream_resp_rdata,
      .downstream_resp_slverr,
      .downstream_resp_decerr
  );

  typedef struct packed {
    logic write;
    logic [AddrWidth-1:0] addr;
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic secure;
    logic privileged;
  } req_t;

  typedef struct packed {
    logic [DataWidth-1:0] rdata;
    logic slverr;
    logic decerr;
  } resp_t;

  req_t  req_upstream;
  req_t  req_downstream;
  resp_t resp_downstream;
  resp_t resp_upstream;
  logic  upstream_req_pending;
  logic  upstream_abort_pending;
  logic  downstream_req_pending;


  assign req_upstream = '{
          write: upstream_req_write,
          addr: upstream_req_addr,
          wdata: upstream_req_wdata,
          wstrb: upstream_req_wstrb,
          secure: upstream_req_secure,
          privileged: upstream_req_privileged
      };

  assign req_downstream = '{
          write: downstream_req_write,
          addr: downstream_req_addr,
          wdata: downstream_req_wdata,
          wstrb: downstream_req_wstrb,
          secure: downstream_req_secure,
          privileged: downstream_req_privileged
      };

  assign resp_downstream = '{
          rdata: downstream_resp_rdata,
          slverr: downstream_resp_slverr,
          decerr: downstream_resp_decerr
      };

  assign resp_upstream = '{
          rdata: upstream_resp_rdata,
          slverr: upstream_resp_slverr,
          decerr: upstream_resp_decerr
      };

  always_ff @(posedge upstream_clk) begin
    if (upstream_rst || upstream_resp_valid) begin
      upstream_req_pending <= 1'b0;
    end else if (upstream_req_valid) begin
      upstream_req_pending <= 1'b1;
    end
  end

  always_ff @(posedge upstream_clk) begin
    if (upstream_rst || upstream_req_abort) begin
      upstream_abort_pending <= 1'b0;
    end else if (upstream_req_valid) begin
      upstream_abort_pending <= 1'b1;
    end
  end

  always_ff @(posedge downstream_clk) begin
    if (downstream_rst || downstream_resp_valid) begin
      downstream_req_pending <= 1'b0;
    end else if (downstream_req_valid) begin
      downstream_req_pending <= 1'b1;
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME_CR(only_one_outstanding_upstream_req_a, upstream_req_pending |-> !upstream_req_valid,
                upstream_clk, upstream_rst)
  `BR_ASSUME_CR(no_spurious_abort_a, upstream_req_abort |-> upstream_abort_pending, upstream_clk,
                upstream_rst)
  `BR_ASSUME_CR(no_spurious_downstream_resp_a, downstream_resp_valid |-> downstream_req_pending,
                downstream_clk, downstream_rst)

  // ----------FV assertions----------
  `BR_ASSERT_CR(no_spurious_upstream_resp_a, upstream_resp_valid |-> upstream_req_pending,
                upstream_clk, upstream_rst)
  `BR_ASSERT_CR(only_one_outstanding_downstream_req_a,
                downstream_req_pending |-> !downstream_req_valid, downstream_clk, downstream_rst)

  // ----------Payload integrity checks----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH($bits(req_t)),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0)
  ) req_sb (
      .incoming_clk(upstream_clk),
      .outgoing_clk(downstream_clk),
      .rstN(!rst),
      .incoming_vld(upstream_req_valid),
      .incoming_data(req_upstream),
      .outgoing_vld(downstream_req_valid && !downstream_rst),
      .outgoing_data(req_downstream)
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH($bits(resp_t)),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0)
  ) resp_sb (
      .incoming_clk(downstream_clk),
      .outgoing_clk(upstream_clk),
      .rstN(!rst),
      .incoming_vld(downstream_resp_valid && !downstream_rst),
      .incoming_data(resp_downstream),
      .outgoing_vld(upstream_resp_valid),
      .outgoing_data(resp_upstream)
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(1),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0)
  ) abort_sb (
      .incoming_clk(upstream_clk),
      .outgoing_clk(downstream_clk),
      .rstN(!rst),
      .incoming_vld(upstream_req_abort),
      .incoming_data(1'b1),
      .outgoing_vld(downstream_req_abort && !downstream_rst),
      .outgoing_data(1'b1)
  );

endmodule : br_csr_cdc_fpv_monitor
