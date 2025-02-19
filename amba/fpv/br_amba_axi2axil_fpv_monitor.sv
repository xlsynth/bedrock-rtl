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

// FIFO br_credit_receiver FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "amba4_defines.svh"

module br_amba_axi2axil_fpv_monitor #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int DataWidth = 32,  // Must be at least 32
    parameter int IdWidth = 4,  // Must be at least 1
    parameter int AWUserWidth = 8,  // Must be at least 1
    parameter int ARUserWidth = 8,  // Must be at least 1
    parameter int WUserWidth = 8,  // Must be at least 1
    parameter int BUserWidth = 8,  // Must be at least 1
    parameter int RUserWidth = 8,  // Must be at least 1
    parameter int MaxOutstandingReqs = 16,  // Must be at least 2
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input  logic [                 AddrWidth-1:0] axi_awaddr,
    input  logic [                   IdWidth-1:0] axi_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_awprot,
    input  logic [               AWUserWidth-1:0] axi_awuser,
    input  logic                                  axi_awvalid,
    input logic                                  axi_awready,
    input  logic [                 DataWidth-1:0] axi_wdata,
    input  logic [               StrobeWidth-1:0] axi_wstrb,
    input  logic [                WUserWidth-1:0] axi_wuser,
    input  logic                                  axi_wlast,
    input  logic                                  axi_wvalid,
    input logic                                  axi_wready,
    input logic [                   IdWidth-1:0] axi_bid,
    input logic [                BUserWidth-1:0] axi_buser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_bresp,
    input logic                                  axi_bvalid,
    input  logic                                  axi_bready,
    input  logic [                 AddrWidth-1:0] axi_araddr,
    input  logic [                   IdWidth-1:0] axi_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input  logic [               ARUserWidth-1:0] axi_aruser,
    input  logic                                  axi_arvalid,
    input logic                                  axi_arready,
    input logic [                   IdWidth-1:0] axi_rid,
    input logic [                 DataWidth-1:0] axi_rdata,
    input logic [                RUserWidth-1:0] axi_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_rresp,
    input logic                                  axi_rlast,
    input logic                                  axi_rvalid,
    input  logic                                  axi_rready,

    // AXI4-Lite interface
    input logic [            AddrWidth-1:0] axil_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input logic [          AWUserWidth-1:0] axil_awuser,
    input logic                             axil_awvalid,
    input  logic                             axil_awready,
    input logic [            DataWidth-1:0] axil_wdata,
    input logic [          StrobeWidth-1:0] axil_wstrb,
    input logic [           WUserWidth-1:0] axil_wuser,
    input logic                             axil_wvalid,
    input  logic                             axil_wready,
    input  logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input  logic [           BUserWidth-1:0] axil_buser,
    input  logic                             axil_bvalid,
    input logic                             axil_bready,
    input logic [            AddrWidth-1:0] axil_araddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input logic [          ARUserWidth-1:0] axil_aruser,
    input logic                             axil_arvalid,
    input  logic                             axil_arready,
    input  logic [            DataWidth-1:0] axil_rdata,
    input  logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    input  logic [           RUserWidth-1:0] axil_ruser,
    input  logic                             axil_rvalid,
    input logic                             axil_rready
);

/*
    // Instance of the AXI Slave DUV
    axi_slave axi_duv_slave (
        .aclk          (clk),
        .aresetn       (~rst),
        .awid          (axi_awid),
        .awaddr        (axi_awaddr),
        .awlen         (axi_awlen),
        .awsize        (axi_awsize),
        .awburst       (axi_awburst),
        .awlock        ('d0),
        .awcache       ('d0),
        .awprot        (axi_awprot),
        .awvalid       (axi_awvalid),
        .awready       (axi_awready),
        .awqos         ('d0),
        .awregion      ('d0),
        .awuser        (axi_awuser),
        .ruser         (axi_ruser),
        .arqos         ('d0),
        .arregion      ('d0),
        .aruser        (axi_aruser),
        .buser         (axi_buser),
        .wuser         (axi_wuser),

        .wdata         (axi_wdata),
        .wstrb         (axi_wstrb),
        .wlast         (axi_wlast),
        .wvalid        (axi_wvalid),
        .wready        (axi_wready),

        .bid           (axi_bid),
        .bresp         (axi_bresp),
        .bvalid        (axi_bvalid),
        .bready        (axi_bready),

        .arid          (axi_arid),
        .araddr        (axi_araddr),
        .arlen         (axi_arlen),
        .arsize        (axi_arsize),
        .arburst       (axi_arburst),
        .arlock        ('d0),
        .arcache       ('d0),
        .arprot        (axi_arprot),
        .arvalid       (axi_arvalid),
        .arready       (axi_arready),

        .rid           (axi_rid),
        .rdata         (axi_rdata),
        .rresp         (axi_rresp),
        .rlast         (axi_rlast),
        .rvalid        (axi_rvalid),
        .rready        (axi_rready),

        .csysreq       ('d0),
        .csysack       ('d0),
        .cactive       ('d0)
    );

    defparam axi_duv_slave.ADDR_WIDTH              = AddrWidth;
    defparam axi_duv_slave.DATA_WIDTH              = DataWidth;
    defparam axi_duv_slave.ID_WIDTH                = IdWidth;
    defparam axi_duv_slave.LEN_WIDTH               = br_amba::AxiBurstLenWidth;
    defparam axi_duv_slave.MAX_PENDING             = MaxOutstandingReqs;
*/

endmodule : br_amba_axi2axil_fpv_monitor

bind br_amba_axi2axil br_amba_axi2axil_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstandingReqs(MaxOutstandingReqs)
) monitor (.*);
