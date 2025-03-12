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

// Bedrock-RTL AXI4-Lite 1:2 Split FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_split_fpv_monitor #(
    parameter int AddrWidth = 40,  // Must be at least 12
    parameter int DataWidth = 64,  // Must be at least 32
    parameter int AWUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter int MaxOutstandingReads = 1,  // Must be at least 1
    parameter int MaxOutstandingWrites = 1,  // Must be at least 1
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset
    input logic [AddrWidth-1:0] branch_start_addr,
    input logic [AddrWidth-1:0] branch_end_addr,

    // AXI4-Lite root target interface
    input logic [            AddrWidth-1:0] root_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] root_awprot,
    input logic [          AWUserWidth-1:0] root_awuser,
    input logic                             root_awvalid,
    input logic                             root_awready,
    input logic [            DataWidth-1:0] root_wdata,
    input logic [          StrobeWidth-1:0] root_wstrb,
    input logic [           WUserWidth-1:0] root_wuser,
    input logic                             root_wvalid,
    input logic                             root_wready,
    input logic [br_amba::AxiRespWidth-1:0] root_bresp,
    input logic                             root_bvalid,
    input logic                             root_bready,
    input logic [            AddrWidth-1:0] root_araddr,
    input logic [br_amba::AxiProtWidth-1:0] root_arprot,
    input logic [          ARUserWidth-1:0] root_aruser,
    input logic                             root_arvalid,
    input logic                             root_arready,
    input logic [            DataWidth-1:0] root_rdata,
    input logic [br_amba::AxiRespWidth-1:0] root_rresp,
    input logic [           RUserWidth-1:0] root_ruser,
    input logic                             root_rvalid,
    input logic                             root_rready,

    // AXI4-Lite trunk initiator interface
    input logic [            AddrWidth-1:0] trunk_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] trunk_awprot,
    input logic [          AWUserWidth-1:0] trunk_awuser,
    input logic                             trunk_awvalid,
    input logic                             trunk_awready,
    input logic [            DataWidth-1:0] trunk_wdata,
    input logic [          StrobeWidth-1:0] trunk_wstrb,
    input logic [           WUserWidth-1:0] trunk_wuser,
    input logic                             trunk_wvalid,
    input logic                             trunk_wready,
    input logic [br_amba::AxiRespWidth-1:0] trunk_bresp,
    input logic                             trunk_bvalid,
    input logic                             trunk_bready,
    input logic [            AddrWidth-1:0] trunk_araddr,
    input logic [br_amba::AxiProtWidth-1:0] trunk_arprot,
    input logic [          ARUserWidth-1:0] trunk_aruser,
    input logic                             trunk_arvalid,
    input logic                             trunk_arready,
    input logic [            DataWidth-1:0] trunk_rdata,
    input logic [br_amba::AxiRespWidth-1:0] trunk_rresp,
    input logic [           RUserWidth-1:0] trunk_ruser,
    input logic                             trunk_rvalid,
    input logic                             trunk_rready,

    // AXI4-Lite branch initiator interface
    input logic [            AddrWidth-1:0] branch_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] branch_awprot,
    input logic [          AWUserWidth-1:0] branch_awuser,
    input logic                             branch_awvalid,
    input logic                             branch_awready,
    input logic [            DataWidth-1:0] branch_wdata,
    input logic [          StrobeWidth-1:0] branch_wstrb,
    input logic [           WUserWidth-1:0] branch_wuser,
    input logic                             branch_wvalid,
    input logic                             branch_wready,
    input logic [br_amba::AxiRespWidth-1:0] branch_bresp,
    input logic                             branch_bvalid,
    input logic                             branch_bready,
    input logic [            AddrWidth-1:0] branch_araddr,
    input logic [br_amba::AxiProtWidth-1:0] branch_arprot,
    input logic [          ARUserWidth-1:0] branch_aruser,
    input logic                             branch_arvalid,
    input logic                             branch_arready,
    input logic [            DataWidth-1:0] branch_rdata,
    input logic [br_amba::AxiRespWidth-1:0] branch_rresp,
    input logic [           RUserWidth-1:0] branch_ruser,
    input logic                             branch_rvalid,
    input logic                             branch_rready
);

  // ----------FV assumptions----------
  `BR_ASSUME(branch_start_end_addr_a, branch_start_addr < branch_end_addr)
  // root
  `BR_ASSUME(branch_start_addr_stable_a, $stable(branch_start_addr))
  `BR_ASSUME(branch_end_addr_stable_a, $stable(branch_end_addr))

  // AXI4-Lite root target interface
  axi4_master #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING_RD(MaxOutstandingReads),
      .MAX_PENDING_WR(MaxOutstandingWrites)
  ) root (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (root_awvalid),
      .awready (root_awready),
      .awuser  (root_awuser),
      .awaddr  (root_awaddr),
      .awprot  (root_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (root_wvalid),
      .wready  (root_wready),
      .wuser   (root_wuser),
      .wdata   (root_wdata),
      .wstrb   (root_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (root_bvalid),
      .bready  (root_bready),
      .buser   (root_buser),
      .bresp   (root_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (root_arvalid),
      .arready (root_arready),
      .araddr  (root_araddr),
      .aruser  (root_aruser),
      .arprot  (root_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (root_rvalid),
      .rready  (root_rready),
      .ruser   (root_ruser),
      .rdata   (root_rdata),
      .rresp   (root_rresp),
      .rid     (),
      .rlast   ()
  );

  // AXI4-Lite trunk initiator interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING_RD(MaxOutstandingReads),
      .MAX_PENDING_WR(MaxOutstandingWrites)
  ) trunk (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (trunk_awvalid),
      .awready (trunk_awready),
      .awuser  (trunk_awuser),
      .awaddr  (trunk_awaddr),
      .awprot  (trunk_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (trunk_wvalid),
      .wready  (trunk_wready),
      .wuser   (trunk_wuser),
      .wdata   (trunk_wdata),
      .wstrb   (trunk_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (trunk_bvalid),
      .bready  (trunk_bready),
      .buser   (trunk_buser),
      .bresp   (trunk_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (trunk_arvalid),
      .arready (trunk_arready),
      .araddr  (trunk_araddr),
      .aruser  (trunk_aruser),
      .arprot  (trunk_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (trunk_rvalid),
      .rready  (trunk_rready),
      .ruser   (trunk_ruser),
      .rdata   (trunk_rdata),
      .rresp   (trunk_rresp),
      .rid     (),
      .rlast   ()
  );

  // AXI4-Lite branch initiator interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING_RD(MaxOutstandingReads),
      .MAX_PENDING_WR(MaxOutstandingWrites)
  ) branch (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (branch_awvalid),
      .awready (branch_awready),
      .awuser  (branch_awuser),
      .awaddr  (branch_awaddr),
      .awprot  (branch_awprot),
      .awid    ('d0),
      .awlen   ('d0),
      .awsize  (),                // (DataWidth> 8) ? $clog2(DataWidth/8) : 1
      .awburst ('d0),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      // Write Channel
      .wvalid  (branch_wvalid),
      .wready  (branch_wready),
      .wuser   (branch_wuser),
      .wdata   (branch_wdata),
      .wstrb   (branch_wstrb),
      .wlast   ('d1),
      // Write Response channel
      .bvalid  (branch_bvalid),
      .bready  (branch_bready),
      .buser   (branch_buser),
      .bresp   (branch_bresp),
      .bid     ('d0),
      // Read Address Channel
      .arvalid (branch_arvalid),
      .arready (branch_arready),
      .araddr  (branch_araddr),
      .aruser  (branch_aruser),
      .arprot  (branch_arprot),
      .arid    ('d0),
      .arlen   ('d0),
      .arsize  (),                // (DataWidth> 8) ? $clog2(DataWidth/8) : 1
      .arburst ('d0),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      // Read Channel
      .rvalid  (branch_rvalid),
      .rready  (branch_rready),
      .ruser   (branch_ruser),
      .rdata   (branch_rdata),
      .rresp   (branch_rresp),
      .rid     ('d0),
      .rlast   ('d1)
  );

endmodule : br_amba_axil_split_fpv_monitor

bind br_amba_axil_split br_amba_axil_split_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstandingReads(MaxOutstandingReads),
    .MaxOutstandingWrites(MaxOutstandingWrites)
) monitor (.*);
