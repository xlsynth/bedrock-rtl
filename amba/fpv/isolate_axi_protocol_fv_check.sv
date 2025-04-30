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

`include "br_asserts.svh"
`include "br_registers.svh"

module isolate_axi_protocol_fv_check #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 1,
    parameter int AWUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int BUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter int MaxOutstanding = 128,
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    localparam int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen),
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic                                  clk,
    input logic                                  rst,
    input logic                                  upstream_rst,
    input logic                                  downstream_rst,
    //
    input logic                                  isolate_req,
    input logic                                  isolate_done,
    //
    input logic [                 AddrWidth-1:0] upstream_awaddr,
    input logic [                   IdWidth-1:0] upstream_awid,
    input logic [          AxiBurstLenWidth-1:0] upstream_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
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

  // FV 4-phase handshake modeling
  fv_4phase_handshake #(
      .Master(1)
  ) isolate_req_handshake (
      .clk(clk),
      .rst(rst),
      .req(isolate_req),
      .ack(isolate_done)
  );

  // upstream
  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxOutstanding)
  ) upstream (
      // Global signals
      .aclk    (clk),
      .aresetn (!upstream_rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (upstream_awvalid),
      .awready (upstream_awready),
      .awid    (upstream_awid),
      .awaddr  (upstream_awaddr),
      .awlen   (upstream_awlen),
      .awsize  (upstream_awsize),
      .awburst (upstream_awburst),
      .awuser  (upstream_awuser),
      .awprot  (upstream_awprot),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (upstream_wvalid),
      .wready  (upstream_wready),
      .wdata   (upstream_wdata),
      .wstrb   (upstream_wstrb),
      .wlast   (upstream_wlast),
      .wuser   (upstream_wuser),
      // Write Response channel
      .bvalid  (upstream_bvalid),
      .bready  (upstream_bready),
      .bid     (upstream_bid),
      .bresp   (upstream_bresp),
      .buser   (upstream_buser),
      // Read Address Channel
      .arvalid (upstream_arvalid),
      .arready (upstream_arready),
      .arid    (upstream_arid),
      .araddr  (upstream_araddr),
      .arlen   (upstream_arlen),
      .arsize  (upstream_arsize),
      .arburst (upstream_arburst),
      .aruser  (upstream_aruser),
      .arprot  (upstream_arprot),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (upstream_rvalid),
      .rready  (upstream_rready),
      .ruser   (upstream_ruser),
      .rid     (upstream_rid),
      .rdata   (upstream_rdata),
      .rresp   (upstream_rresp),
      .rlast   (upstream_rlast)
  );

  // downstream
  axi4_slave #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxOutstanding)
  ) downstream (
      // Global signals
      .aclk    (clk),
      .aresetn (!downstream_rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (downstream_awvalid),
      .awready (downstream_awready),
      .awid    (downstream_awid),
      .awaddr  (downstream_awaddr),
      .awlen   (downstream_awlen),
      .awsize  (downstream_awsize),
      .awburst (downstream_awburst),
      .awuser  (downstream_awuser),
      .awprot  (downstream_awprot),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      // Write Channel
      .wvalid  (downstream_wvalid),
      .wready  (downstream_wready),
      .wdata   (downstream_wdata),
      .wstrb   (downstream_wstrb),
      .wlast   (downstream_wlast),
      .wuser   (downstream_wuser),
      // Write Response channel
      .bvalid  (downstream_bvalid),
      .bready  (downstream_bready),
      .bid     (downstream_bid),
      .bresp   (downstream_bresp),
      .buser   (downstream_buser),
      // Read Address Channel
      .arvalid (downstream_arvalid),
      .arready (downstream_arready),
      .arid    (downstream_arid),
      .araddr  (downstream_araddr),
      .arlen   (downstream_arlen),
      .arsize  (downstream_arsize),
      .arburst (downstream_arburst),
      .aruser  (downstream_aruser),
      .arprot  (downstream_arprot),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      // Read Channel
      .rvalid  (downstream_rvalid),
      .rready  (downstream_rready),
      .ruser   (downstream_ruser),
      .rid     (downstream_rid),
      .rdata   (downstream_rdata),
      .rresp   (downstream_rresp),
      .rlast   (downstream_rlast)
  );

endmodule
