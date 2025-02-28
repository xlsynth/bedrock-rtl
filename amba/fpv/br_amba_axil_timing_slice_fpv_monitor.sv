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

// AXI4-Lite Timing Slice

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil_timing_slice_fpv_monitor #(
    parameter  int AddrWidth   = 40,
    parameter  int DataWidth   = 64,
    parameter  int AWUserWidth = 1,
    parameter  int WUserWidth  = 1,
    parameter  int ARUserWidth = 1,
    parameter  int RUserWidth  = 1,
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite target interface
    input logic [            AddrWidth-1:0] target_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] target_awprot,
    input logic [          AWUserWidth-1:0] target_awuser,
    input logic                             target_awvalid,
    input logic                             target_awready,
    input logic [            DataWidth-1:0] target_wdata,
    input logic [          StrobeWidth-1:0] target_wstrb,
    input logic [           WUserWidth-1:0] target_wuser,
    input logic                             target_wvalid,
    input logic                             target_wready,
    input logic [br_amba::AxiRespWidth-1:0] target_bresp,
    input logic                             target_bvalid,
    input logic                             target_bready,
    input logic [            AddrWidth-1:0] target_araddr,
    input logic [br_amba::AxiProtWidth-1:0] target_arprot,
    input logic [          ARUserWidth-1:0] target_aruser,
    input logic                             target_arvalid,
    input logic                             target_arready,
    input logic [            DataWidth-1:0] target_rdata,
    input logic [br_amba::AxiRespWidth-1:0] target_rresp,
    input logic [           RUserWidth-1:0] target_ruser,
    input logic                             target_rvalid,
    input logic                             target_rready,

    // AXI4-Lite initiator interface
    input logic [            AddrWidth-1:0] init_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] init_awprot,
    input logic [          AWUserWidth-1:0] init_awuser,
    input logic                             init_awvalid,
    input logic                             init_awready,
    input logic [            DataWidth-1:0] init_wdata,
    input logic [          StrobeWidth-1:0] init_wstrb,
    input logic [           WUserWidth-1:0] init_wuser,
    input logic                             init_wvalid,
    input logic                             init_wready,
    input logic [br_amba::AxiRespWidth-1:0] init_bresp,
    input logic                             init_bvalid,
    input logic                             init_bready,
    input logic [            AddrWidth-1:0] init_araddr,
    input logic [br_amba::AxiProtWidth-1:0] init_arprot,
    input logic [          ARUserWidth-1:0] init_aruser,
    input logic                             init_arvalid,
    input logic                             init_arready,
    input logic [            DataWidth-1:0] init_rdata,
    input logic [br_amba::AxiRespWidth-1:0] init_rresp,
    input logic [           RUserWidth-1:0] init_ruser,
    input logic                             init_rvalid,
    input logic                             init_rready
);

  // AXI4-Lite target interface
  axi4_ace_slave #(
      .ADDR_WIDTH  (AddrWidth),
      .DATA_WIDTH  (DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH (WUserWidth),
      .RUSER_WIDTH (RUserWidth)
  ) target (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq ('d0),
      .csysack ('d0),
      .cactive ('d0),
      // Write Address Channel
      .awvalid (target_awvalid),
      .awready (target_awready),
      .awaddr  (target_awaddr),
      .awuser  (target_awuser),
      .awprot  (target_awprot),
      .awid    ('d0),
      .awlen   ('d0),
      .awsize  ('d0),
      .awburst ('d0),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      .awunique('d0),
      .awdomain('d0),
      .awsnoop ('d0),
      .awbar   ('d0),
      // Write Channel
      .wvalid  (target_wvalid),
      .wready  (target_wready),
      .wdata   (target_wdata),
      .wstrb   (target_wstrb),
      .wuser   (target_wuser),
      .wlast   ('d0),
      .wack    ('d0),
      // Write Response channel
      .bvalid  (target_bvalid),
      .bready  (target_bready),
      .bresp   (target_bresp),
      .bid     ('d0),
      .buser   ('d0),
      // Read Address Channel
      .arvalid (target_arvalid),
      .arready (target_arready),
      .araddr  (target_araddr),
      .aruser  (target_aruser),
      .arlock  (target_arprot),
      .arid    ('d0),
      .arlen   ('d0),
      .arsize  ('d0),
      .arburst ('d0),
      .arcache ('d0),
      .arprot  ('d0),
      .arqos   ('d0),
      .arregion('d0),
      .ardomain('d0),
      .arsnoop ('d0),
      .arbar   ('d0),
      // Read Channel
      .rvalid  (target_rvalid),
      .rready  (target_rready),
      .ruser   (target_ruser),
      .rdata   (target_rdata),
      .rresp   (target_rresp),
      .rid     ('d0),
      .rack    ('d0),
      .acvalid ('d0),
      .acready ('d0),
      .acaddr  ('d0),
      .acprot  ('d0),
      .acsnoop ('d0),
      .cdvalid ('d0),
      .cdready ('d0),
      .cddata  ('d0),
      .cdlast  ('d0),
      .crvalid ('d0),
      .crready ('d0),
      .crresp  ('d0),
      .rlast   ('d0)
  );

  // AXI4-Lite initiator interface
  axi4_ace_master #(
      .ADDR_WIDTH  (AddrWidth),
      .DATA_WIDTH  (DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH (WUserWidth),
      .RUSER_WIDTH (RUserWidth)
  ) init (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq ('d0),
      .csysack ('d0),
      .cactive ('d0),
      // Write Address Channel
      .awvalid (init_awvalid),
      .awready (init_awready),
      .awaddr  (init_awaddr),
      .awuser  (init_awuser),
      .awprot  (init_awprot),
      .awid    ('d0),
      .awlen   ('d0),
      .awsize  ('d0),
      .awburst ('d0),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      .awunique('d0),
      .awdomain('d0),
      .awsnoop ('d0),
      .awbar   ('d0),
      // Write Channel
      .wvalid  (init_wvalid),
      .wready  (init_wready),
      .wdata   (init_wdata),
      .wstrb   (init_wstrb),
      .wuser   (init_wuser),
      .wlast   ('d0),
      .wack    ('d0),
      // Write Response channel
      .bvalid  (init_bvalid),
      .bready  (init_bready),
      .bresp   (init_bresp),
      .bid     ('d0),
      .buser   ('d0),
      // Read Address Channel
      .arvalid (init_arvalid),
      .arready (init_arready),
      .araddr  (init_araddr),
      .aruser  (init_aruser),
      .arlock  (init_arprot),
      .arid    ('d0),
      .arlen   ('d0),
      .arsize  ('d0),
      .arburst ('d0),
      .arcache ('d0),
      .arprot  ('d0),
      .arqos   ('d0),
      .arregion('d0),
      .ardomain('d0),
      .arsnoop ('d0),
      .arbar   ('d0),
      // Read Channel
      .rvalid  (init_rvalid),
      .rready  (init_rready),
      .ruser   (init_ruser),
      .rdata   (init_rdata),
      .rresp   (init_rresp),
      .rid     ('d0),
      .rack    ('d0),
      .acvalid ('d0),
      .acready ('d0),
      .acaddr  ('d0),
      .acprot  ('d0),
      .acsnoop ('d0),
      .cdvalid ('d0),
      .cdready ('d0),
      .cddata  ('d0),
      .cdlast  ('d0),
      .crvalid ('d0),
      .crready ('d0),
      .crresp  ('d0),
      .rlast   ('d0)
  );

endmodule : br_amba_axil_timing_slice_fpv_monitor

bind br_amba_axil_timing_slice br_amba_axil_timing_slice_fpv_monitor #(
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth (WUserWidth),
    .RUserWidth (RUserWidth)
) monitor (.*);
