// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

module br_amba_axi_shrinker_tb;
  localparam int TimeoutCycles = 100;
  localparam int AddrWidth = 12;
  localparam int WideDataWidth = 32;
  localparam int NarrowDataWidth = 8;
  localparam int IdWidth = 2;
  localparam int AWUserWidth = 1;
  localparam int ARUserWidth = 1;
  localparam int WUserWidth = 1;
  localparam int BUserWidth = 1;
  localparam int RUserWidth = 1;
  localparam int MaxOutstandingReqs = 4;
  localparam int WriteFifoDepth = 2;
  localparam bit RegisterNarrowOutputs = 0;
  localparam bit RegisterWideOutputs = 0;
  localparam int WideStrobeWidth = WideDataWidth / 8;
  localparam int NarrowStrobeWidth = NarrowDataWidth / 8;

  logic clk;
  logic rst;

  logic [AddrWidth-1:0] wide_awaddr;
  logic [IdWidth-1:0] wide_awid;
  logic [AxiBurstLenWidth-1:0] wide_awlen;
  logic [AxiBurstSizeWidth-1:0] wide_awsize;
  logic [AxiBurstTypeWidth-1:0] wide_awburst;
  logic [AxiProtWidth-1:0] wide_awprot;
  logic [AWUserWidth-1:0] wide_awuser;
  logic wide_awvalid;
  logic wide_awready;

  logic [WideDataWidth-1:0] wide_wdata;
  logic [WideStrobeWidth-1:0] wide_wstrb;
  logic [WUserWidth-1:0] wide_wuser;
  logic wide_wlast;
  logic wide_wvalid;
  logic wide_wready;

  logic [IdWidth-1:0] wide_bid;
  logic [BUserWidth-1:0] wide_buser;
  logic [AxiRespWidth-1:0] wide_bresp;
  logic wide_bvalid;
  logic wide_bready = 1'b1;

  logic [AddrWidth-1:0] wide_araddr;
  logic [IdWidth-1:0] wide_arid;
  logic [AxiBurstLenWidth-1:0] wide_arlen;
  logic [AxiBurstSizeWidth-1:0] wide_arsize;
  logic [AxiBurstTypeWidth-1:0] wide_arburst;
  logic [AxiProtWidth-1:0] wide_arprot;
  logic [ARUserWidth-1:0] wide_aruser;
  logic wide_arvalid;
  logic wide_arready;

  logic [IdWidth-1:0] wide_rid;
  logic [WideDataWidth-1:0] wide_rdata;
  logic [RUserWidth-1:0] wide_ruser;
  logic [AxiRespWidth-1:0] wide_rresp;
  logic wide_rlast;
  logic wide_rvalid;
  logic wide_rready;

  logic [AddrWidth-1:0] narrow_awaddr;
  logic [IdWidth-1:0] narrow_awid;
  logic [AxiBurstLenWidth-1:0] narrow_awlen;
  logic [AxiBurstSizeWidth-1:0] narrow_awsize;
  logic [AxiBurstTypeWidth-1:0] narrow_awburst;
  logic [AxiProtWidth-1:0] narrow_awprot;
  logic [AWUserWidth-1:0] narrow_awuser;
  logic narrow_awvalid;
  logic narrow_awready;

  logic [NarrowDataWidth-1:0] narrow_wdata;
  logic [NarrowStrobeWidth-1:0] narrow_wstrb;
  logic [WUserWidth-1:0] narrow_wuser;
  logic narrow_wlast;
  logic narrow_wvalid;
  logic narrow_wready;

  logic [IdWidth-1:0] narrow_bid;
  logic [BUserWidth-1:0] narrow_buser;
  logic [AxiRespWidth-1:0] narrow_bresp;
  logic narrow_bvalid;
  logic narrow_bready;

  logic [AddrWidth-1:0] narrow_araddr;
  logic [IdWidth-1:0] narrow_arid;
  logic [AxiBurstLenWidth-1:0] narrow_arlen;
  logic [AxiBurstSizeWidth-1:0] narrow_arsize;
  logic [AxiBurstTypeWidth-1:0] narrow_arburst;
  logic [AxiProtWidth-1:0] narrow_arprot;
  logic [ARUserWidth-1:0] narrow_aruser;
  logic narrow_arvalid;
  logic narrow_arready;

  logic [IdWidth-1:0] narrow_rid;
  logic [NarrowDataWidth-1:0] narrow_rdata;
  logic [RUserWidth-1:0] narrow_ruser;
  logic [AxiRespWidth-1:0] narrow_rresp;
  logic narrow_rlast;
  logic narrow_rvalid;
  logic narrow_rready;

  br_amba_axi_shrinker #(
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
  ) dut (
      .clk(clk),
      .rst(rst),
      .wide_awaddr(wide_awaddr),
      .wide_awid(wide_awid),
      .wide_awlen(wide_awlen),
      .wide_awsize(wide_awsize),
      .wide_awburst(wide_awburst),
      .wide_awprot(wide_awprot),
      .wide_awuser(wide_awuser),
      .wide_awvalid(wide_awvalid),
      .wide_awready(wide_awready),
      .wide_wdata(wide_wdata),
      .wide_wstrb(wide_wstrb),
      .wide_wuser(wide_wuser),
      .wide_wlast(wide_wlast),
      .wide_wvalid(wide_wvalid),
      .wide_wready(wide_wready),
      .wide_bid(wide_bid),
      .wide_buser(wide_buser),
      .wide_bresp(wide_bresp),
      .wide_bvalid(wide_bvalid),
      .wide_bready(wide_bready),
      .wide_araddr(wide_araddr),
      .wide_arid(wide_arid),
      .wide_arlen(wide_arlen),
      .wide_arsize(wide_arsize),
      .wide_arburst(wide_arburst),
      .wide_arprot(wide_arprot),
      .wide_aruser(wide_aruser),
      .wide_arvalid(wide_arvalid),
      .wide_arready(wide_arready),
      .wide_rid(wide_rid),
      .wide_rdata(wide_rdata),
      .wide_ruser(wide_ruser),
      .wide_rresp(wide_rresp),
      .wide_rlast(wide_rlast),
      .wide_rvalid(wide_rvalid),
      .wide_rready(wide_rready),
      .narrow_awaddr(narrow_awaddr),
      .narrow_awid(narrow_awid),
      .narrow_awlen(narrow_awlen),
      .narrow_awsize(narrow_awsize),
      .narrow_awburst(narrow_awburst),
      .narrow_awprot(narrow_awprot),
      .narrow_awuser(narrow_awuser),
      .narrow_awvalid(narrow_awvalid),
      .narrow_awready(narrow_awready),
      .narrow_wdata(narrow_wdata),
      .narrow_wstrb(narrow_wstrb),
      .narrow_wuser(narrow_wuser),
      .narrow_wlast(narrow_wlast),
      .narrow_wvalid(narrow_wvalid),
      .narrow_wready(narrow_wready),
      .narrow_bid(narrow_bid),
      .narrow_buser(narrow_buser),
      .narrow_bresp(narrow_bresp),
      .narrow_bvalid(narrow_bvalid),
      .narrow_bready(narrow_bready),
      .narrow_araddr(narrow_araddr),
      .narrow_arid(narrow_arid),
      .narrow_arlen(narrow_arlen),
      .narrow_arsize(narrow_arsize),
      .narrow_arburst(narrow_arburst),
      .narrow_arprot(narrow_arprot),
      .narrow_aruser(narrow_aruser),
      .narrow_arvalid(narrow_arvalid),
      .narrow_arready(narrow_arready),
      .narrow_rid(narrow_rid),
      .narrow_rdata(narrow_rdata),
      .narrow_ruser(narrow_ruser),
      .narrow_rresp(narrow_rresp),
      .narrow_rlast(narrow_rlast),
      .narrow_rvalid(narrow_rvalid),
      .narrow_rready(narrow_rready)
  );

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk(clk),
      .rst(rst)
  );

  task automatic check_eq(input logic [63:0] actual, input logic [63:0] expected,
                          input string message);
    td.check(actual === expected, $sformatf(
             "%s: expected 0x%0h got 0x%0h", message, expected, actual));
  endtask

  task automatic send_wide_aw(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiProtWidth-1:0] prot, input logic [AWUserWidth-1:0] user);
    int timeout = 0;

    @(negedge clk);
    wide_awaddr = addr;
    wide_awid = id;
    wide_awlen = len;
    wide_awsize = size;
    wide_awburst = AxiBurstIncr;
    wide_awprot = prot;
    wide_awuser = user;
    wide_awvalid = 1'b1;
    while (!wide_awready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for wide AW ready");
    @(negedge clk);
    wide_awvalid = 1'b0;
    wide_awaddr = '0;
    wide_awid = '0;
    wide_awlen = '0;
    wide_awsize = '0;
    wide_awburst = '0;
    wide_awprot = '0;
    wide_awuser = '0;
  endtask

  task automatic expect_narrow_aw(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiProtWidth-1:0] prot, input logic [AWUserWidth-1:0] user);
    int timeout = 0;
    narrow_awready = 1'b1;
    while (!narrow_awvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for narrow AW valid");
    check_eq(narrow_awaddr, addr, "narrow_awaddr mismatch");
    check_eq(narrow_awid, id, "narrow_awid mismatch");
    check_eq(narrow_awlen, len, "narrow_awlen mismatch");
    check_eq(narrow_awsize, size, "narrow_awsize mismatch");
    check_eq(narrow_awburst, AxiBurstIncr, "narrow_awburst mismatch");
    check_eq(narrow_awprot, prot, "narrow_awprot mismatch");
    check_eq(narrow_awuser, user, "narrow_awuser mismatch");
    @(negedge clk);
    narrow_awready = 1'b0;
  endtask

  task automatic send_wide_w(input logic [WideDataWidth-1:0] data,
                             input logic [WideStrobeWidth-1:0] strb, input logic last,
                             input logic [WUserWidth-1:0] user);
    int timeout = 0;

    @(negedge clk);
    wide_wdata  = data;
    wide_wstrb  = strb;
    wide_wlast  = last;
    wide_wuser  = user;
    wide_wvalid = 1'b1;

    while (!wide_wready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for wide W ready");

    @(negedge clk);
    wide_wvalid = 1'b0;
    wide_wdata  = '0;
    wide_wstrb  = '0;
    wide_wlast  = 1'b0;
    wide_wuser  = '0;
  endtask

  task automatic expect_narrow_w(input logic [NarrowDataWidth-1:0] data,
                                 input logic [NarrowStrobeWidth-1:0] strb, input logic last,
                                 input logic [WUserWidth-1:0] user);
    int timeout = 0;
    narrow_wready = 1'b1;
    while (!narrow_wvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for narrow W valid");
    check_eq(narrow_wdata, data, "narrow_wdata mismatch");
    check_eq(narrow_wstrb, strb, "narrow_wstrb mismatch");
    check_eq(narrow_wuser, user, "narrow_wuser mismatch");
    check_eq(narrow_wlast, last, "narrow_wlast mismatch");
    @(negedge clk);
    narrow_wready = 1'b0;
  endtask

  task automatic send_narrow_b(input logic [IdWidth-1:0] id, input logic [AxiRespWidth-1:0] resp,
                               input logic [BUserWidth-1:0] user);
    int timeout = 0;
    @(negedge clk);
    narrow_bid = id;
    narrow_bresp = resp;
    narrow_buser = user;
    narrow_bvalid = 1'b1;
    while (!narrow_bready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for narrow B ready");
    @(negedge clk);
    narrow_bvalid = 1'b0;
    narrow_bid = '0;
    narrow_bresp = '0;
    narrow_buser = '0;
  endtask

  task automatic expect_wide_b(input logic [IdWidth-1:0] id, input logic [AxiRespWidth-1:0] resp,
                               input logic [BUserWidth-1:0] user);
    int timeout = 0;
    wide_bready = 1'b1;
    while (!wide_bvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for wide B valid");
    check_eq(wide_bid, id, "wide_bid mismatch");
    check_eq(wide_bresp, resp, "wide_bresp mismatch");
    check_eq(wide_buser, user, "wide_buser mismatch");
    @(negedge clk);
    wide_bready = 1'b0;
  endtask

  task automatic send_wide_ar(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiProtWidth-1:0] prot, input logic [ARUserWidth-1:0] user);
    int timeout = 0;

    @(negedge clk);
    wide_araddr = addr;
    wide_arid = id;
    wide_arlen = len;
    wide_arsize = size;
    wide_arburst = AxiBurstIncr;
    wide_arprot = prot;
    wide_aruser = user;
    wide_arvalid = 1'b1;

    while (!wide_arready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for wide AR ready");

    @(negedge clk);
    wide_arvalid = 1'b0;
    wide_araddr = '0;
    wide_arid = '0;
    wide_arlen = '0;
    wide_arsize = '0;
    wide_arburst = '0;
    wide_arprot = '0;
    wide_aruser = '0;
  endtask

  task automatic expect_narrow_ar(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiProtWidth-1:0] prot, input logic [ARUserWidth-1:0] user);
    int timeout = 0;
    narrow_arready = 1'b1;
    while (!narrow_arvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for narrow AR valid");

    check_eq(narrow_araddr, addr, "narrow_araddr mismatch");
    check_eq(narrow_arid, id, "narrow_arid mismatch");
    check_eq(narrow_arlen, len, "narrow_arlen mismatch");
    check_eq(narrow_arsize, size, "narrow_arsize mismatch");
    check_eq(narrow_arburst, AxiBurstIncr, "narrow_arburst mismatch");
    check_eq(narrow_arprot, prot, "narrow_arprot mismatch");
    check_eq(narrow_aruser, user, "narrow_aruser mismatch");

    @(negedge clk);
    narrow_arready = 1'b0;
  endtask

  task automatic send_narrow_r(input logic [IdWidth-1:0] id, input logic [NarrowDataWidth-1:0] data,
                               input logic [AxiRespWidth-1:0] resp, input logic last,
                               input logic [RUserWidth-1:0] user);
    int timeout = 0;

    @(negedge clk);
    narrow_rid = id;
    narrow_rdata = data;
    narrow_rresp = resp;
    narrow_rlast = last;
    narrow_ruser = user;
    narrow_rvalid = 1'b1;

    while (!narrow_rready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for narrow R ready");

    @(negedge clk);
    narrow_rvalid = 1'b0;
    narrow_rid = '0;
    narrow_rdata = '0;
    narrow_rresp = '0;
    narrow_rlast = 1'b0;
    narrow_ruser = '0;
  endtask

  task automatic expect_wide_r(input logic [IdWidth-1:0] id, input logic [WideDataWidth-1:0] data,
                               input logic [AxiRespWidth-1:0] resp, input logic last,
                               input logic [RUserWidth-1:0] user);
    int timeout = 0;
    wide_rready = 1'b1;
    while (!wide_rvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for wide R valid");

    check_eq(wide_rid, id, "wide_rid mismatch");
    check_eq(wide_rdata, data, "wide_rdata mismatch");
    check_eq(wide_rresp, resp, "wide_rresp mismatch");
    check_eq(wide_ruser, user, "wide_ruser mismatch");
    check_eq(wide_rlast, last, "wide_rlast mismatch");

    @(negedge clk);
    wide_rready = 1'b0;
  endtask

  initial begin
    wide_awvalid = 1'b0;
    wide_awaddr = '0;
    wide_awid = '0;
    wide_awlen = '0;
    wide_awsize = '0;
    wide_awburst = '0;
    wide_awprot = '0;
    wide_awuser = '0;
    wide_wvalid = 1'b0;
    wide_wdata = '0;
    wide_wstrb = '0;
    wide_wlast = 1'b0;
    wide_wuser = '0;
    wide_bready = 1'b1;
    wide_arvalid = 1'b0;
    wide_araddr = '0;
    wide_arid = '0;
    wide_arlen = '0;
    wide_arsize = '0;
    wide_arburst = '0;
    wide_arprot = '0;
    wide_aruser = '0;
    wide_rready = 1'b1;
    narrow_awready = 1'b0;
    narrow_wready = 1'b0;
    narrow_bvalid = 1'b0;
    narrow_bresp = '0;
    narrow_buser = '0;
    narrow_arready = 1'b0;
    narrow_rvalid = 1'b0;
    narrow_rid = '0;
    narrow_rdata = '0;
    narrow_rresp = '0;
    narrow_rlast = 1'b0;
    narrow_ruser = '0;
    $assertoff;
    td.reset_dut();
    td.wait_cycles(2);
    $asserton;

    $display("Checking shrinking write transaction");
    fork
      send_wide_aw(12'h120, 2'b01, 8'h01, 3'd2, 3'b101, 1'b1);
      expect_narrow_aw(12'h120, 2'b01, 8'h07, 3'd0, 3'b101, 1'b1);
    join

    fork
      begin
        send_wide_w(32'h44332211, 4'b1111, 1'b0, 1'b1);
        send_wide_w(32'h88776655, 4'b1111, 1'b1, 1'b1);
      end
      begin
        expect_narrow_w(8'h11, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h22, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h33, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h44, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h55, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h66, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h77, 1'b1, 1'b0, 1'b1);
        expect_narrow_w(8'h88, 1'b1, 1'b1, 1'b1);
      end
    join

    fork
      send_narrow_b(2'b01, AxiRespOkay, 1'b1);
      expect_wide_b(2'b01, AxiRespOkay, 1'b1);
    join

    $display("Checking narrow-sized write lane selection");
    fork
      send_wide_aw(12'h102, 2'b10, 8'h00, 3'd0, 3'b001, 1'b0);
      expect_narrow_aw(12'h102, 2'b10, 8'h00, 3'd0, 3'b001, 1'b0);
    join

    fork
      send_wide_w(32'h44332211, 4'b0100, 1'b1, 1'b0);
      expect_narrow_w(8'h33, 1'b1, 1'b1, 1'b0);
    join

    fork
      send_narrow_b(2'b10, AxiRespSlverr, 1'b0);
      expect_wide_b(2'b10, AxiRespSlverr, 1'b0);
    join

    $display("Checking shrinking read transaction");
    fork
      send_wide_ar(12'h040, 2'b11, 8'h01, 3'd2, 3'b110, 1'b1);
      expect_narrow_ar(12'h040, 2'b11, 8'h07, 3'd0, 3'b110, 1'b1);
    join

    fork
      begin
        send_narrow_r(2'b11, 8'h01, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h02, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h03, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h04, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h05, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h06, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h07, AxiRespOkay, 1'b0, 1'b1);
        send_narrow_r(2'b11, 8'h08, AxiRespOkay, 1'b1, 1'b1);
      end
      begin
        expect_wide_r(2'b11, 32'h04030201, AxiRespOkay, 1'b0, 1'b1);
        expect_wide_r(2'b11, 32'h08070605, AxiRespOkay, 1'b1, 1'b1);
      end
    join

    $display("Checking narrow-sized read lane placement");
    fork
      send_wide_ar(12'h043, 2'b00, 8'h00, 3'd0, 3'b011, 1'b0);
      expect_narrow_ar(12'h043, 2'b00, 8'h00, 3'd0, 3'b011, 1'b0);
    join

    fork
      send_narrow_r(2'b00, 8'hAB, AxiRespDecerr, 1'b1, 1'b0);
      expect_wide_r(2'b00, 32'hAB000000, AxiRespDecerr, 1'b1, 1'b0);
    join

    // TODO(zhemao): Add additional test cases
    // - Narrowing read/write transaction where the size is smaller than 32 bits
    // - Multi-beat read/write transactions that are not narrowed

    td.finish();
  end

endmodule
