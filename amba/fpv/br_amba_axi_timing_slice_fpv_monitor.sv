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

// AXI4 Timing Slice FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_timing_slice_fpv_monitor #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be 32, 64, or 128
    parameter int IdWidth = 1,  // Must be at least 1
    parameter int AWUserWidth = 1,  // Must be at least 1
    parameter int WUserWidth = 1,  // Must be at least 1
    parameter int ARUserWidth = 1,  // Must be at least 1
    parameter int BUserWidth = 1,  // Must be at least 1
    parameter int RUserWidth = 1,  // Must be at least 1
    parameter int AWSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int WSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int ARSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int RSliceType = 2,  // 0: forward, 1: reverse, 2: full
    parameter int BSliceType = 2,  // 0: forward, 1: reverse, 2: full
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 target interface
    input logic [                 AddrWidth-1:0] target_awaddr,
    input logic [                   IdWidth-1:0] target_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] target_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] target_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] target_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] target_awprot,
    input logic [               AWUserWidth-1:0] target_awuser,
    input logic                                  target_awvalid,
    input logic                                  target_awready,
    input logic [                 DataWidth-1:0] target_wdata,
    input logic [               StrobeWidth-1:0] target_wstrb,
    input logic [                WUserWidth-1:0] target_wuser,
    input logic                                  target_wlast,
    input logic                                  target_wvalid,
    input logic                                  target_wready,
    input logic [                   IdWidth-1:0] target_bid,
    input logic [                BUserWidth-1:0] target_buser,
    input logic [     br_amba::AxiRespWidth-1:0] target_bresp,
    input logic                                  target_bvalid,
    input logic                                  target_bready,
    input logic [                 AddrWidth-1:0] target_araddr,
    input logic [                   IdWidth-1:0] target_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] target_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] target_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] target_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] target_arprot,
    input logic [               ARUserWidth-1:0] target_aruser,
    input logic                                  target_arvalid,
    input logic                                  target_arready,
    input logic [                   IdWidth-1:0] target_rid,
    input logic [                 DataWidth-1:0] target_rdata,
    input logic [                RUserWidth-1:0] target_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] target_rresp,
    input logic                                  target_rlast,
    input logic                                  target_rvalid,
    input logic                                  target_rready,

    // AXI4 initiator interface
    input logic [                 AddrWidth-1:0] init_awaddr,
    input logic [                   IdWidth-1:0] init_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] init_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] init_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] init_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] init_awprot,
    input logic [               AWUserWidth-1:0] init_awuser,
    input logic                                  init_awvalid,
    input logic                                  init_awready,
    input logic [                 DataWidth-1:0] init_wdata,
    input logic [               StrobeWidth-1:0] init_wstrb,
    input logic [                WUserWidth-1:0] init_wuser,
    input logic                                  init_wlast,
    input logic                                  init_wvalid,
    input logic                                  init_wready,
    input logic [                   IdWidth-1:0] init_bid,
    input logic [                BUserWidth-1:0] init_buser,
    input logic [     br_amba::AxiRespWidth-1:0] init_bresp,
    input logic                                  init_bvalid,
    input logic                                  init_bready,
    input logic [                 AddrWidth-1:0] init_araddr,
    input logic [                   IdWidth-1:0] init_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] init_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] init_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] init_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] init_arprot,
    input logic [               ARUserWidth-1:0] init_aruser,
    input logic                                  init_arvalid,
    input logic                                  init_arready,
    input logic [                   IdWidth-1:0] init_rid,
    input logic [                 DataWidth-1:0] init_rdata,
    input logic [                RUserWidth-1:0] init_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] init_rresp,
    input logic                                  init_rlast,
    input logic                                  init_rvalid,
    input logic                                  init_rready
);

  // AXI4 target interface
  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth)
  ) target (
      // Global signals
      .aclk    (clk),
      .aresetn (~rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (target_awvalid),
      .awready (target_awready),
      .awid    (target_awid),
      .awaddr  (target_awaddr),
      .awlen   (target_awlen),
      .awsize  (target_awsize),
      .awburst (target_awburst),
      .awuser  (target_awuser),
      .awprot  (target_awprot),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      // Write Channel
      .wvalid  (target_wvalid),
      .wready  (target_wready),
      .wdata   (target_wdata),
      .wstrb   (target_wstrb),
      .wlast   (target_wlast),
      .wuser   (target_wuser),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .bid     (target_bid),
      .bresp   (target_bresp),
      .buser   (target_buser),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .arid    (target_arid),
      .araddr  (target_araddr),
      .arlen   (target_arlen),
      .arsize  (target_arsize),
      .arburst (target_arburst),
      .aruser  (target_aruser),
      .arprot  (target_arprot),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      // Read Channel
      .rvalid  (target_rvalid),
      .rready  (target_rready),
      .ruser   (target_ruser),
      .rid     (target_rid),
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .rlast   (target_rlast)
  );

  // AXI4 initiator interface
  axi4_slave #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth)
  ) init (
      // Global signals
      .aclk    (clk),
      .aresetn (~rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (init_awvalid),
      .awready (init_awready),
      .awid    (init_awid),
      .awaddr  (init_awaddr),
      .awlen   (init_awlen),
      .awsize  (init_awsize),
      .awburst (init_awburst),
      .awuser  (init_awuser),
      .awprot  (init_awprot),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      // Write Channel
      .wvalid  (init_wvalid),
      .wready  (init_wready),
      .wdata   (init_wdata),
      .wstrb   (init_wstrb),
      .wlast   (init_wlast),
      .wuser   (init_wuser),
      // Write Response channel
      .bvalid  (init_bvalid),
      .bready  (init_bready),
      .bid     (init_bid),
      .bresp   (init_bresp),
      .buser   (init_buser),
      // Read Address Channel
      .arvalid (init_arvalid),
      .arready (init_arready),
      .arid    (init_arid),
      .araddr  (init_araddr),
      .arlen   (init_arlen),
      .arsize  (init_arsize),
      .arburst (init_arburst),
      .aruser  (init_aruser),
      .arprot  (init_arprot),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      // Read Channel
      .rvalid  (init_rvalid),
      .rready  (init_rready),
      .ruser   (init_ruser),
      .rid     (init_rid),
      .rdata   (init_rdata),
      .rresp   (init_rresp),
      .rlast   (init_rlast)
  );

endmodule : br_amba_axi_timing_slice_fpv_monitor

bind br_amba_axi_timing_slice br_amba_axi_timing_slice_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .AWSliceType(AWSliceType),
    .WSliceType(WSliceType),
    .ARSliceType(ARSliceType),
    .RSliceType(RSliceType),
    .BSliceType(BSliceType)
) monitor (.*);
