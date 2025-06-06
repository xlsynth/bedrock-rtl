// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Bedrock-RTL AXI4 to AXI4-Lite Bridge FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_isolate_mgr_fpv_monitor #(
    // Width of the AXI address field.
    parameter int AddrWidth = 12,
    // Width of the AXI data field.
    parameter int DataWidth = 32,
    // Width of the AXI ID field.
    parameter int IdWidth = 1,
    // Width of the AXI AWUSER field.
    parameter int AWUserWidth = 1,
    // Width of the AXI WUSER field.
    parameter int WUserWidth = 1,
    // Width of the AXI ARUSER field.
    parameter int ARUserWidth = 1,
    // Width of the AXI BUSER field.
    parameter int BUserWidth = 1,
    // Width of the AXI RUSER field.
    parameter int RUserWidth = 1,
    // Maximum number of outstanding requests that can be tracked
    // without backpressuring the upstream request ports. Must be at least 2.
    parameter int MaxOutstanding = 128,
    // Maximum allowed skew (measured in max-length transactions)
    // that can be tracked between AW and W channels without causing
    // backpressure on the upstream ports.
    parameter int MaxTransactionSkew = 2,
    // Maximum number of response beats per transaction. Can be set
    // to 1 for AXI-Lite, otherwise must be set to
    // br_amba::AxiBurstLenWidth.
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    // WUSER data to generate for isolated transactions.
    parameter bit [WUserWidth-1:0] IsolateWUser = '0,
    // WDATA data to generate for isolated transactions.
    parameter bit [DataWidth-1:0] IsolateWData = '0,
    // WSTRB data to generate for isolated transactions.
    parameter bit [(DataWidth/8)-1:0] IsolateWStrb = '0,
    localparam int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen),
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic                                  clk,
    input logic                                  rst,
    //
    input logic                                  isolate_req,
    input logic                                  isolate_done,
    //
    input logic [                 AddrWidth-1:0] upstream_awaddr,
    input logic [                   IdWidth-1:0] upstream_awid,
    input logic [          AxiBurstLenWidth-1:0] upstream_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
    input logic [    br_amba::AxiCacheWidth-1:0] upstream_awcache,
    input logic [     br_amba::AxiProtWidth-1:0] upstream_awprot,
    input logic [               AWUserWidth-1:0] upstream_awuser,
    input logic                                  upstream_awvalid,
    input logic                                  upstream_awready,
    input logic [                 DataWidth-1:0] upstream_wdata,
    input logic [               StrobeWidth-1:0] upstream_wstrb,
    input logic [                WUserWidth-1:0] upstream_wuser,
    input logic                                  upstream_wlast,
    input logic                                  upstream_wvalid,
    input logic                                  upstream_wready,
    input logic [                   IdWidth-1:0] upstream_bid,
    input logic [                BUserWidth-1:0] upstream_buser,
    input logic [     br_amba::AxiRespWidth-1:0] upstream_bresp,
    input logic                                  upstream_bvalid,
    input logic                                  upstream_bready,
    input logic [                 AddrWidth-1:0] upstream_araddr,
    input logic [                   IdWidth-1:0] upstream_arid,
    input logic [          AxiBurstLenWidth-1:0] upstream_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_arburst,
    input logic [    br_amba::AxiCacheWidth-1:0] upstream_arcache,
    input logic [     br_amba::AxiProtWidth-1:0] upstream_arprot,
    input logic [               ARUserWidth-1:0] upstream_aruser,
    input logic                                  upstream_arvalid,
    input logic                                  upstream_arready,
    input logic [                   IdWidth-1:0] upstream_rid,
    input logic [                 DataWidth-1:0] upstream_rdata,
    input logic [                RUserWidth-1:0] upstream_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] upstream_rresp,
    input logic                                  upstream_rlast,
    input logic                                  upstream_rvalid,
    input logic                                  upstream_rready,
    //
    input logic [                 AddrWidth-1:0] downstream_awaddr,
    input logic [                   IdWidth-1:0] downstream_awid,
    input logic [          AxiBurstLenWidth-1:0] downstream_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] downstream_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] downstream_awburst,
    input logic [    br_amba::AxiCacheWidth-1:0] downstream_awcache,
    input logic [     br_amba::AxiProtWidth-1:0] downstream_awprot,
    input logic [               AWUserWidth-1:0] downstream_awuser,
    input logic                                  downstream_awvalid,
    input logic                                  downstream_awready,
    input logic [                 DataWidth-1:0] downstream_wdata,
    input logic [               StrobeWidth-1:0] downstream_wstrb,
    input logic [                WUserWidth-1:0] downstream_wuser,
    input logic                                  downstream_wlast,
    input logic                                  downstream_wvalid,
    input logic                                  downstream_wready,
    input logic [                   IdWidth-1:0] downstream_bid,
    input logic [                BUserWidth-1:0] downstream_buser,
    input logic [     br_amba::AxiRespWidth-1:0] downstream_bresp,
    input logic                                  downstream_bvalid,
    input logic                                  downstream_bready,
    input logic [                 AddrWidth-1:0] downstream_araddr,
    input logic [                   IdWidth-1:0] downstream_arid,
    input logic [          AxiBurstLenWidth-1:0] downstream_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] downstream_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] downstream_arburst,
    input logic [    br_amba::AxiCacheWidth-1:0] downstream_arcache,
    input logic [     br_amba::AxiProtWidth-1:0] downstream_arprot,
    input logic [               ARUserWidth-1:0] downstream_aruser,
    input logic                                  downstream_arvalid,
    input logic                                  downstream_arready,
    input logic [                   IdWidth-1:0] downstream_rid,
    input logic [                 DataWidth-1:0] downstream_rdata,
    input logic [                RUserWidth-1:0] downstream_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] downstream_rresp,
    input logic                                  downstream_rlast,
    input logic                                  downstream_rvalid,
    input logic                                  downstream_rready
);

  // during this window, upstream won't be AXI protocol compliant
  // However, downstream should still behave fine
  logic iso_flg;
  assign iso_flg = isolate_req && isolate_done;

  // for AXI_LITE, there is no awlen.
  // Therefore upstream_awlen is a random signal without any constraint from ABVIP
  if (MaxAxiBurstLen == 1) begin : gen_axi_lite
    `BR_ASSUME(upstream_awlen0_axilite_a, upstream_awvalid |-> upstream_awlen == 'd0)
  end

  // deadlock check
  `BR_ASSERT(req_eventually_done_a, isolate_req |-> s_eventually isolate_done)
  `BR_ASSERT(eventually_back_to_normal_a, $fell(isolate_req) |-> s_eventually $fell(isolate_done))

  isolate_axi_protocol_fv_check #(
      .ReadInterleaveOn(1),
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .MaxOutstanding(MaxOutstanding),
      .MaxAxiBurstLen(MaxAxiBurstLen)
  ) fv_axi_check (
      .clk,
      .rst,
      .upstream_rst  (rst | iso_flg),
      .downstream_rst(rst),
      .isolate_req,
      .isolate_done,
      .upstream_awaddr,
      .upstream_awid,
      .upstream_awlen,
      .upstream_awsize,
      .upstream_awburst,
      .upstream_awcache,
      .upstream_awprot,
      .upstream_awuser,
      .upstream_awvalid,
      .upstream_awready,
      .upstream_wdata,
      .upstream_wstrb,
      .upstream_wuser,
      .upstream_wlast,
      .upstream_wvalid,
      .upstream_wready,
      .upstream_bid,
      .upstream_buser,
      .upstream_bresp,
      .upstream_bvalid,
      .upstream_bready,
      .upstream_araddr,
      .upstream_arid,
      .upstream_arlen,
      .upstream_arsize,
      .upstream_arburst,
      .upstream_arcache,
      .upstream_arprot,
      .upstream_aruser,
      .upstream_arvalid,
      .upstream_arready,
      .upstream_rid,
      .upstream_rdata,
      .upstream_ruser,
      .upstream_rresp,
      .upstream_rlast,
      .upstream_rvalid,
      .upstream_rready,
      .downstream_awaddr,
      .downstream_awid,
      .downstream_awlen,
      .downstream_awsize,
      .downstream_awburst,
      .downstream_awcache,
      .downstream_awprot,
      .downstream_awuser,
      .downstream_awvalid,
      .downstream_awready,
      .downstream_wdata,
      .downstream_wstrb,
      .downstream_wuser,
      .downstream_wlast,
      .downstream_wvalid,
      .downstream_wready,
      .downstream_bid,
      .downstream_buser,
      .downstream_bresp,
      .downstream_bvalid,
      .downstream_bready,
      .downstream_araddr,
      .downstream_arid,
      .downstream_arlen,
      .downstream_arsize,
      .downstream_arburst,
      .downstream_arcache,
      .downstream_arprot,
      .downstream_aruser,
      .downstream_arvalid,
      .downstream_arready,
      .downstream_rid,
      .downstream_rdata,
      .downstream_ruser,
      .downstream_rresp,
      .downstream_rlast,
      .downstream_rvalid,
      .downstream_rready
  );


endmodule : br_amba_axi_isolate_mgr_fpv_monitor

bind br_amba_axi_isolate_mgr br_amba_axi_isolate_mgr_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .WUserWidth(WUserWidth),
    .ARUserWidth(ARUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstanding(MaxOutstanding),
    .MaxTransactionSkew(MaxTransactionSkew),
    .MaxAxiBurstLen(MaxAxiBurstLen),
    .IsolateWUser(IsolateWUser),
    .IsolateWData(IsolateWData),
    .IsolateWStrb(IsolateWStrb)
) monitor (.*);
