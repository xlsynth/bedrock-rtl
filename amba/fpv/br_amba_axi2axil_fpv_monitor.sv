// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4 to AXI4-Lite Bridge FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi2axil_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 4,
    parameter int AWUserWidth = 8,
    parameter int ARUserWidth = 8,
    parameter int WUserWidth = 8,
    parameter int BUserWidth = 8,
    parameter int RUserWidth = 8,
    parameter int MaxOutstandingReqs = 16,
    localparam int StrobeWidth = DataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // AXI4 interface
    input logic [                 AddrWidth-1:0] axi_awaddr,
    input logic [                   IdWidth-1:0] axi_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] axi_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] axi_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] axi_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] axi_awprot,
    input logic [               AWUserWidth-1:0] axi_awuser,
    input logic                                  axi_awvalid,
    input logic                                  axi_awready,
    input logic [                 DataWidth-1:0] axi_wdata,
    input logic [               StrobeWidth-1:0] axi_wstrb,
    input logic [                WUserWidth-1:0] axi_wuser,
    input logic                                  axi_wlast,
    input logic                                  axi_wvalid,
    input logic                                  axi_wready,
    input logic [                   IdWidth-1:0] axi_bid,
    input logic [                BUserWidth-1:0] axi_buser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_bresp,
    input logic                                  axi_bvalid,
    input logic                                  axi_bready,
    input logic [                 AddrWidth-1:0] axi_araddr,
    input logic [                   IdWidth-1:0] axi_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] axi_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] axi_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] axi_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] axi_arprot,
    input logic [               ARUserWidth-1:0] axi_aruser,
    input logic                                  axi_arvalid,
    input logic                                  axi_arready,
    input logic [                   IdWidth-1:0] axi_rid,
    input logic [                 DataWidth-1:0] axi_rdata,
    input logic [                RUserWidth-1:0] axi_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] axi_rresp,
    input logic                                  axi_rlast,
    input logic                                  axi_rvalid,
    input logic                                  axi_rready,

    // AXI4-Lite interface
    input logic [            AddrWidth-1:0] axil_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input logic [          AWUserWidth-1:0] axil_awuser,
    input logic                             axil_awvalid,
    input logic                             axil_awready,
    input logic [            DataWidth-1:0] axil_wdata,
    input logic [          StrobeWidth-1:0] axil_wstrb,
    input logic [           WUserWidth-1:0] axil_wuser,
    input logic                             axil_wvalid,
    input logic                             axil_wready,
    input logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input logic [           BUserWidth-1:0] axil_buser,
    input logic                             axil_bvalid,
    input logic                             axil_bready,
    input logic [            AddrWidth-1:0] axil_araddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input logic [          ARUserWidth-1:0] axil_aruser,
    input logic                             axil_arvalid,
    input logic                             axil_arready,
    input logic [            DataWidth-1:0] axil_rdata,
    input logic [br_amba::AxiRespWidth-1:0] axil_rresp,
    input logic [           RUserWidth-1:0] axil_ruser,
    input logic                             axil_rvalid,
    input logic                             axil_rready
);

  // ABVIP should send more than DUT to test backpressure
  localparam int MaxPending = MaxOutstandingReqs + 2;

  // multi-beat narrow access is NOT supported.
  `BR_ASSUME(no_multi_beat_narrow_access_write_a, axi_awvalid && (axi_awsize != $clog2(StrobeWidth)
                                                  ) |-> axi_awlen == 'd0)
  `BR_ASSUME(no_multi_beat_narrow_access_read_a, axi_arvalid && (axi_arsize != $clog2(StrobeWidth)
                                                 ) |-> axi_arlen == 'd0)

  // Instance of the AXI Slave DUV
  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      // when there is no valid, ready doesn't have to be high eventually
      // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
      // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) axi4 (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (axi_awvalid),
      .awready (axi_awready),
      .awid    (axi_awid),
      .awaddr  (axi_awaddr),
      .awlen   (axi_awlen),
      .awsize  (axi_awsize),
      .awburst (axi_awburst),
      .awuser  (axi_awuser),
      .awprot  (axi_awprot),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (axi_wvalid),
      .wready  (axi_wready),
      .wdata   (axi_wdata),
      .wstrb   (axi_wstrb),
      .wlast   (axi_wlast),
      .wuser   (axi_wuser),
      // Write Response channel
      .bvalid  (axi_bvalid),
      .bready  (axi_bready),
      .bid     (axi_bid),
      .bresp   (axi_bresp),
      .buser   (axi_buser),
      // Read Address Channel
      .arvalid (axi_arvalid),
      .arready (axi_arready),
      .arid    (axi_arid),
      .araddr  (axi_araddr),
      .arlen   (axi_arlen),
      .arsize  (axi_arsize),
      .arburst (axi_arburst),
      .aruser  (axi_aruser),
      .arprot  (axi_arprot),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (axi_rvalid),
      .rready  (axi_rready),
      .ruser   (axi_ruser),
      .rid     (axi_rid),
      .rdata   (axi_rdata),
      .rresp   (axi_rresp),
      .rlast   (axi_rlast)
  );

  // AXI4-Lite interface
  axi4_slave #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      // when there is no valid, ready doesn't have to be high eventually
      // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
      // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
  ) axi4_lite (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      // Write Address Channel
      .awvalid (axil_awvalid),
      .awready (axil_awready),
      .awuser  (axil_awuser),
      .awaddr  (axil_awaddr),
      .awprot  (axil_awprot),
      .awid    (),
      .awlen   (),
      .awsize  (),
      .awburst (),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (axil_wvalid),
      .wready  (axil_wready),
      .wuser   (axil_wuser),
      .wdata   (axil_wdata),
      .wstrb   (axil_wstrb),
      .wlast   (),
      // Write Response channel
      .bvalid  (axil_bvalid),
      .bready  (axil_bready),
      .buser   (axil_buser),
      .bresp   (axil_bresp),
      .bid     (),
      // Read Address Channel
      .arvalid (axil_arvalid),
      .arready (axil_arready),
      .araddr  (axil_araddr),
      .aruser  (axil_aruser),
      .arprot  (axil_arprot),
      .arid    (),
      .arlen   (),
      .arsize  (),
      .arburst (),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (axil_rvalid),
      .rready  (axil_rready),
      .ruser   (axil_ruser),
      .rdata   (axil_rdata),
      .rresp   (axil_rresp),
      .rid     (),
      .rlast   ()
  );

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
