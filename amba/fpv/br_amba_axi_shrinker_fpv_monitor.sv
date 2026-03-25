// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4 Shrinker FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_shrinker_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int WideDataWidth = 16,
    parameter int NarrowDataWidth = 8,
    parameter int IdWidth = 1,
    parameter int AWUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int BUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter int MaxOutstandingReqs = 1,
    parameter int WriteFifoDepth = 1,
    parameter bit RegisterNarrowOutputs = 1,
    parameter bit RegisterWideOutputs = 1,
    localparam int WideStrobeWidth = WideDataWidth / 8,
    localparam int NarrowStrobeWidth = NarrowDataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Wide AXI4 target interface
    input logic [                 AddrWidth-1:0] wide_awaddr,
    input logic [                   IdWidth-1:0] wide_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] wide_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] wide_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] wide_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] wide_awprot,
    input logic [               AWUserWidth-1:0] wide_awuser,
    input logic                                  wide_awvalid,
    input logic                                  wide_awready,
    input logic [             WideDataWidth-1:0] wide_wdata,
    input logic [           WideStrobeWidth-1:0] wide_wstrb,
    input logic [                WUserWidth-1:0] wide_wuser,
    input logic                                  wide_wlast,
    input logic                                  wide_wvalid,
    input logic                                  wide_wready,
    input logic [                   IdWidth-1:0] wide_bid,
    input logic [                BUserWidth-1:0] wide_buser,
    input logic [     br_amba::AxiRespWidth-1:0] wide_bresp,
    input logic                                  wide_bvalid,
    input logic                                  wide_bready,
    input logic [                 AddrWidth-1:0] wide_araddr,
    input logic [                   IdWidth-1:0] wide_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] wide_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] wide_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] wide_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] wide_arprot,
    input logic [               ARUserWidth-1:0] wide_aruser,
    input logic                                  wide_arvalid,
    input logic                                  wide_arready,
    input logic [                   IdWidth-1:0] wide_rid,
    input logic [             WideDataWidth-1:0] wide_rdata,
    input logic [                RUserWidth-1:0] wide_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] wide_rresp,
    input logic                                  wide_rlast,
    input logic                                  wide_rvalid,
    input logic                                  wide_rready,

    // Narrow AXI4 initiator interface
    input logic [                 AddrWidth-1:0] narrow_awaddr,
    input logic [                   IdWidth-1:0] narrow_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] narrow_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] narrow_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] narrow_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] narrow_awprot,
    input logic [               AWUserWidth-1:0] narrow_awuser,
    input logic                                  narrow_awvalid,
    input logic                                  narrow_awready,
    input logic [           NarrowDataWidth-1:0] narrow_wdata,
    input logic [         NarrowStrobeWidth-1:0] narrow_wstrb,
    input logic [                WUserWidth-1:0] narrow_wuser,
    input logic                                  narrow_wlast,
    input logic                                  narrow_wvalid,
    input logic                                  narrow_wready,
    input logic [                   IdWidth-1:0] narrow_bid,
    input logic [                BUserWidth-1:0] narrow_buser,
    input logic [     br_amba::AxiRespWidth-1:0] narrow_bresp,
    input logic                                  narrow_bvalid,
    input logic                                  narrow_bready,
    input logic [                 AddrWidth-1:0] narrow_araddr,
    input logic [                   IdWidth-1:0] narrow_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] narrow_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] narrow_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] narrow_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] narrow_arprot,
    input logic [               ARUserWidth-1:0] narrow_aruser,
    input logic                                  narrow_arvalid,
    input logic                                  narrow_arready,
    input logic [                   IdWidth-1:0] narrow_rid,
    input logic [           NarrowDataWidth-1:0] narrow_rdata,
    input logic [                RUserWidth-1:0] narrow_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] narrow_rresp,
    input logic                                  narrow_rlast,
    input logic                                  narrow_rvalid,
    input logic                                  narrow_rready
);

  localparam int WideSizeLog2 = $clog2(WideStrobeWidth);
  localparam int NarrowSizeLog2 = $clog2(NarrowStrobeWidth);

  // ABVIP should send more than DUT to test backpressure.
  localparam int MaxPending = MaxOutstandingReqs + WriteFifoDepth + 2;
  // When there is no valid, ready does not need to rise eventually.
  localparam bit ValidBeforeReady = 1;

  `BR_ASSUME(
      shrinking_awburst_incr_a,
      (wide_awvalid && wide_awsize > NarrowSizeLog2) |-> wide_awburst == br_amba::AxiBurstIncr)
  `BR_ASSUME(
      shrinking_arburst_incr_a,
      (wide_arvalid && wide_arsize > NarrowSizeLog2) |-> wide_arburst == br_amba::AxiBurstIncr)

  // Make sure wide len and size won't result in narrow len overflowing
  localparam int ExtBurstLenWidth = br_amba::AxiBurstLenWidth + WideSizeLog2 - NarrowSizeLog2;
  localparam int MaxBurstLen = 2 ** br_amba::AxiBurstLenWidth - 1;

  logic [ExtBurstLenWidth-1:0] ext_wide_awlen;
  logic [ExtBurstLenWidth-1:0] ext_wide_arlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_awlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_arlen;

  assign ext_wide_awlen = ExtBurstLenWidth'(wide_awlen);
  assign ext_wide_arlen = ExtBurstLenWidth'(wide_arlen);

  assign ext_narrow_awlen =
      (wide_awsize > NarrowSizeLog2) ?
      ((ext_wide_awlen + 1'b1) << (wide_awsize - NarrowSizeLog2)) - 1'b1 : ext_wide_awlen;
  assign ext_narrow_arlen =
      (wide_arsize > NarrowSizeLog2) ?
      ((ext_wide_arlen + 1'b1) << (wide_arsize - NarrowSizeLog2)) - 1'b1 : ext_wide_arlen;

  `BR_ASSUME(narrow_awlen_no_overflow_a, wide_awvalid |-> ext_narrow_awlen <= MaxBurstLen)
  `BR_ASSUME(narrow_arlen_no_overflow_a, wide_arvalid |-> ext_narrow_arlen <= MaxBurstLen)

  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(WideDataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(ValidBeforeReady),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1),
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0)
  ) wide (
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      .awvalid (wide_awvalid),
      .awready (wide_awready),
      .awid    (wide_awid),
      .awaddr  (wide_awaddr),
      .awlen   (wide_awlen),
      .awsize  (wide_awsize),
      .awburst (wide_awburst),
      .awuser  (wide_awuser),
      .awprot  (wide_awprot),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      .wvalid  (wide_wvalid),
      .wready  (wide_wready),
      .wdata   (wide_wdata),
      .wstrb   (wide_wstrb),
      .wlast   (wide_wlast),
      .wuser   (wide_wuser),
      .bvalid  (wide_bvalid),
      .bready  (wide_bready),
      .bid     (wide_bid),
      .bresp   (wide_bresp),
      .buser   (wide_buser),
      .arvalid (wide_arvalid),
      .arready (wide_arready),
      .arid    (wide_arid),
      .araddr  (wide_araddr),
      .arlen   (wide_arlen),
      .arsize  (wide_arsize),
      .arburst (wide_arburst),
      .aruser  (wide_aruser),
      .arprot  (wide_arprot),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      .rvalid  (wide_rvalid),
      .rready  (wide_rready),
      .ruser   (wide_ruser),
      .rid     (wide_rid),
      .rdata   (wide_rdata),
      .rresp   (wide_rresp),
      .rlast   (wide_rlast)
  );

  axi4_slave #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(NarrowDataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(ValidBeforeReady),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1),
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0)
  ) narrow (
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      .awvalid (narrow_awvalid),
      .awready (narrow_awready),
      .awid    (narrow_awid),
      .awaddr  (narrow_awaddr),
      .awlen   (narrow_awlen),
      .awsize  (narrow_awsize),
      .awburst (narrow_awburst),
      .awuser  (narrow_awuser),
      .awprot  (narrow_awprot),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      .wvalid  (narrow_wvalid),
      .wready  (narrow_wready),
      .wdata   (narrow_wdata),
      .wstrb   (narrow_wstrb),
      .wlast   (narrow_wlast),
      .wuser   (narrow_wuser),
      .bvalid  (narrow_bvalid),
      .bready  (narrow_bready),
      .bid     (narrow_bid),
      .bresp   (narrow_bresp),
      .buser   (narrow_buser),
      .arvalid (narrow_arvalid),
      .arready (narrow_arready),
      .arid    (narrow_arid),
      .araddr  (narrow_araddr),
      .arlen   (narrow_arlen),
      .arsize  (narrow_arsize),
      .arburst (narrow_arburst),
      .aruser  (narrow_aruser),
      .arprot  (narrow_arprot),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      .rvalid  (narrow_rvalid),
      .rready  (narrow_rready),
      .ruser   (narrow_ruser),
      .rid     (narrow_rid),
      .rdata   (narrow_rdata),
      .rresp   (narrow_rresp),
      .rlast   (narrow_rlast)
  );

endmodule : br_amba_axi_shrinker_fpv_monitor

bind br_amba_axi_shrinker br_amba_axi_shrinker_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .WideDataWidth(WideDataWidth),
    .NarrowDataWidth(NarrowDataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstandingReqs(MaxOutstandingReqs),
    .WriteFifoDepth(WriteFifoDepth),
    .RegisterNarrowOutputs(RegisterNarrowOutputs),
    .RegisterWideOutputs(RegisterWideOutputs)
) monitor (.*);
