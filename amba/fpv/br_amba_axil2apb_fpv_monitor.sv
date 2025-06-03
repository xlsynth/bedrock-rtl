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

// Bedrock-RTL AXI4-Lite to APB Bridge

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axil2apb_fpv_monitor #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32   // Must be at least 32
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4-Lite interface
    input logic [            AddrWidth-1:0] awaddr,
    input logic [br_amba::AxiProtWidth-1:0] awprot,
    input logic                             awvalid,
    input logic                             awready,
    input logic [            DataWidth-1:0] wdata,
    input logic [        (DataWidth/8)-1:0] wstrb,
    input logic                             wvalid,
    input logic                             wready,
    input logic [br_amba::AxiRespWidth-1:0] bresp,
    input logic                             bvalid,
    input logic                             bready,
    input logic [            AddrWidth-1:0] araddr,
    input logic [br_amba::AxiProtWidth-1:0] arprot,
    input logic                             arvalid,
    input logic                             arready,
    input logic [            DataWidth-1:0] rdata,
    input logic [br_amba::AxiRespWidth-1:0] rresp,
    input logic                             rvalid,
    input logic                             rready,

    // APB interface
    input logic [            AddrWidth-1:0] paddr,
    input logic                             psel,
    input logic                             penable,
    input logic [br_amba::ApbProtWidth-1:0] pprot,
    input logic [        (DataWidth/8)-1:0] pstrb,
    input logic                             pwrite,
    input logic [            DataWidth-1:0] pwdata,
    input logic [            DataWidth-1:0] prdata,
    input logic                             pready,
    input logic                             pslverr
);

  // when there is no valid, ready doesn't have to be high eventually
  // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
  // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
  localparam bit ValidBeforeReady = 1;

  // AXI4-Lite interface
  axi4_master #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(ValidBeforeReady)
  ) axi (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (awvalid),
      .awready (awready),
      .awaddr  (awaddr),
      .awprot  (awprot),
      .awuser  (),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (wvalid),
      .wready  (wready),
      .wdata   (wdata),
      .wstrb   (wstrb),
      .wuser   (),
      .wlast   (),
      // Write Response channel
      .bvalid  (bvalid),
      .bready  (bready),
      .bresp   (bresp),
      .buser   (),
      .bid     (),
      // Read Address Channel
      .arvalid (arvalid),
      .arready (arready),
      .araddr  (araddr),
      .arprot  (arprot),
      .aruser  (),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (rvalid),
      .rready  (rready),
      .rdata   (rdata),
      .rresp   (rresp),
      .ruser   (),
      .rid     (),
      .rlast   ()
  );

  // APB interface
  apb4_slave #(
      .ABUS_WIDTH(AddrWidth),
      .DBUS_WIDTH(DataWidth)
  ) apb (
      .pclk(clk),
      .presetn(!rst),
      .psel,
      .penable,
      .paddr,
      .pwrite,
      .pwdata,
      .pstrb,
      .pprot,
      .pready,
      .prdata,
      .pslverr
  );

endmodule : br_amba_axil2apb_fpv_monitor

bind br_amba_axil2apb br_amba_axil2apb_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth)
) monitor (.*);
