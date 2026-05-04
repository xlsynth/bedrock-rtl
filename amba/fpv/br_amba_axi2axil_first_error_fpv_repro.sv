// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for AXI write-burst response aggregation. The public AXI B response
// must preserve the first non-OKAY response from the split AXI-Lite writes.

import br_amba::*;

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi2axil_first_error_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int AddrWidth = 12;
  localparam int DataWidth = 32;
  localparam int IdWidth = 2;
  localparam int UserWidth = 1;
  localparam int StrobeWidth = DataWidth / 8;

  logic [AddrWidth-1:0] axi_awaddr;
  logic [IdWidth-1:0] axi_awid;
  logic [AxiBurstLenWidth-1:0] axi_awlen;
  logic [AxiBurstSizeWidth-1:0] axi_awsize;
  logic [AxiBurstTypeWidth-1:0] axi_awburst;
  logic [AxiProtWidth-1:0] axi_awprot;
  logic [UserWidth-1:0] axi_awuser;
  logic axi_awvalid;
  logic axi_awready;
  logic [DataWidth-1:0] axi_wdata;
  logic [StrobeWidth-1:0] axi_wstrb;
  logic [UserWidth-1:0] axi_wuser;
  logic axi_wlast;
  logic axi_wvalid;
  logic axi_wready;
  logic [IdWidth-1:0] axi_bid;
  logic [UserWidth-1:0] axi_buser;
  logic [AxiRespWidth-1:0] axi_bresp;
  logic axi_bvalid;
  logic axi_bready;

  logic [AddrWidth-1:0] axil_awaddr;
  logic [AxiProtWidth-1:0] axil_awprot;
  logic [UserWidth-1:0] axil_awuser;
  logic axil_awvalid;
  logic axil_awready;
  logic [DataWidth-1:0] axil_wdata;
  logic [StrobeWidth-1:0] axil_wstrb;
  logic [UserWidth-1:0] axil_wuser;
  logic axil_wvalid;
  logic axil_wready;
  logic [AxiRespWidth-1:0] axil_bresp;
  logic [UserWidth-1:0] axil_buser;
  logic axil_bvalid;
  logic axil_bready;

  logic [1:0] axi_aw_count;
  logic [1:0] axi_w_count;
  logic [1:0] axil_aw_count;
  logic [1:0] axil_w_count;
  logic [1:0] axil_b_count;

  br_amba_axi2axil #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(UserWidth),
      .ARUserWidth(UserWidth),
      .WUserWidth(UserWidth),
      .BUserWidth(UserWidth),
      .RUserWidth(UserWidth),
      .MaxOutstandingReqs(4)
  ) dut (
      .clk,
      .rst,
      .axi_awaddr,
      .axi_awid,
      .axi_awlen,
      .axi_awsize,
      .axi_awburst,
      .axi_awprot,
      .axi_awuser,
      .axi_awvalid,
      .axi_awready,
      .axi_wdata,
      .axi_wstrb,
      .axi_wuser,
      .axi_wlast,
      .axi_wvalid,
      .axi_wready,
      .axi_bid,
      .axi_buser,
      .axi_bresp,
      .axi_bvalid,
      .axi_bready,
      .axi_araddr('0),
      .axi_arid('0),
      .axi_arlen('0),
      .axi_arsize('0),
      .axi_arburst('0),
      .axi_arprot('0),
      .axi_aruser('0),
      .axi_arvalid(1'b0),
      .axi_arready(),
      .axi_rid(),
      .axi_rdata(),
      .axi_ruser(),
      .axi_rresp(),
      .axi_rlast(),
      .axi_rvalid(),
      .axi_rready(1'b1),
      .axil_awaddr,
      .axil_awprot,
      .axil_awuser,
      .axil_awvalid,
      .axil_awready,
      .axil_wdata,
      .axil_wstrb,
      .axil_wuser,
      .axil_wvalid,
      .axil_wready,
      .axil_bresp,
      .axil_buser,
      .axil_bvalid,
      .axil_bready,
      .axil_araddr(),
      .axil_arprot(),
      .axil_aruser(),
      .axil_arvalid(),
      .axil_arready(1'b1),
      .axil_rdata('0),
      .axil_rresp(AxiRespOkay),
      .axil_ruser('0),
      .axil_rvalid(1'b0),
      .axil_rready()
  );

  assign axi_awaddr = 12'h100;
  assign axi_awid = 2'b01;
  assign axi_awlen = 8'd1;
  assign axi_awsize = AxiBurstSizeWidth'($clog2(StrobeWidth));
  assign axi_awburst = AxiBurstIncr;
  assign axi_awprot = '0;
  assign axi_awuser = '0;
  assign axi_awvalid = !rst && (axi_aw_count == 0);
  assign axi_wdata = axi_w_count == 0 ? 32'h1111_0000 : 32'h2222_0000;
  assign axi_wstrb = '1;
  assign axi_wuser = '0;
  assign axi_wlast = axi_w_count == 1;
  assign axi_wvalid = !rst && (axi_w_count < 2);
  assign axi_bready = 1'b1;

  assign axil_awready = 1'b1;
  assign axil_wready = 1'b1;
  assign axil_bvalid = (axil_aw_count == 2) && (axil_w_count == 2) && (axil_b_count < 2);
  assign axil_bresp = axil_b_count == 0 ? AxiRespSlverr : AxiRespDecerr;
  assign axil_buser = '0;

  `BR_REG(axi_aw_count, axi_aw_count + 2'(axi_awvalid && axi_awready))
  `BR_REG(axi_w_count, axi_w_count + 2'(axi_wvalid && axi_wready))
  `BR_REG(axil_aw_count, axil_aw_count + 2'(axil_awvalid && axil_awready))
  `BR_REG(axil_w_count, axil_w_count + 2'(axil_wvalid && axil_wready))
  `BR_REG(axil_b_count, axil_b_count + 2'(axil_bvalid && axil_bready))

  `BR_ASSERT(first_error_preserved_a, axi_bvalid |-> axi_bresp == AxiRespSlverr)

endmodule : br_amba_axi2axil_first_error_fpv_repro
