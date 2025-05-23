`timescale 1ns / 1ps

import br_amba::*;

module br_amba_axi_demux_tb;

  logic clk = 0;
  logic rst = 1;

  // Clock generation
  always #5 clk = ~clk;

  // Parameters for default instantiation
  localparam int NumSubordinates = 2;
  localparam int AwAxiIdWidth = 1;
  localparam int ArAxiIdWidth = 1;
  localparam int AddrWidth = 12;
  localparam int DataWidth = 32;
  localparam int AWUserWidth = 1;
  localparam int WUserWidth = 1;
  localparam int ARUserWidth = 1;
  localparam int BUserWidth = 1;
  localparam int RUserWidth = 1;
  localparam int StrobeWidth = DataWidth / 8;
  localparam int SubIdWidth = $clog2(NumSubordinates);

  // Upstream signals
  logic [SubIdWidth-1:0] upstream_aw_sub_select = '0;
  logic [AddrWidth-1:0] upstream_awaddr = '0;
  logic [AwAxiIdWidth-1:0] upstream_awid = '0;
  logic [AxiBurstLenWidth-1:0] upstream_awlen = '0;
  logic [AxiBurstSizeWidth-1:0] upstream_awsize = '0;
  logic [AxiBurstTypeWidth-1:0] upstream_awburst = '0;
  logic [AxiCacheWidth-1:0] upstream_awcache = '0;
  logic [AxiProtWidth-1:0] upstream_awprot = '0;
  logic [AWUserWidth-1:0] upstream_awuser = '0;
  logic upstream_awvalid = 1'b0;
  logic [DataWidth-1:0] upstream_wdata = '0;
  logic [StrobeWidth-1:0] upstream_wstrb = '0;
  logic [WUserWidth-1:0] upstream_wuser = '0;
  logic upstream_wlast = 1'b0;
  logic upstream_wvalid = 1'b0;
  logic upstream_bready = 1'b0;
  logic [SubIdWidth-1:0] upstream_ar_sub_select = '0;
  logic [AddrWidth-1:0] upstream_araddr = '0;
  logic [ArAxiIdWidth-1:0] upstream_arid = '0;
  logic [AxiBurstLenWidth-1:0] upstream_arlen = '0;
  logic [AxiBurstSizeWidth-1:0] upstream_arsize = '0;
  logic [AxiBurstTypeWidth-1:0] upstream_arburst = '0;
  logic [AxiCacheWidth-1:0] upstream_arcache = '0;
  logic [AxiProtWidth-1:0] upstream_arprot = '0;
  logic [ARUserWidth-1:0] upstream_aruser = '0;
  logic upstream_arvalid = 1'b0;
  logic upstream_rready = 1'b0;

  // Downstream signals
  logic [NumSubordinates-1:0] downstream_awready = '0;
  logic [NumSubordinates-1:0] downstream_wready = '0;
  logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_bid = '0;
  logic [NumSubordinates-1:0][BUserWidth-1:0] downstream_buser = '0;
  logic [NumSubordinates-1:0][AxiRespWidth-1:0] downstream_bresp = '0;
  logic [NumSubordinates-1:0] downstream_bvalid = '0;
  logic [NumSubordinates-1:0] downstream_arready = '0;
  logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_rid = '0;
  logic [NumSubordinates-1:0][DataWidth-1:0] downstream_rdata = '0;
  logic [NumSubordinates-1:0][RUserWidth-1:0] downstream_ruser = '0;
  logic [NumSubordinates-1:0][AxiRespWidth-1:0] downstream_rresp = '0;
  logic [NumSubordinates-1:0] downstream_rlast = '0;
  logic [NumSubordinates-1:0] downstream_rvalid = '0;

  // Outputs from DUT (unused in this TB)
  logic [AwAxiIdWidth-1:0] upstream_bid;
  logic [BUserWidth-1:0] upstream_buser;
  logic [AxiRespWidth-1:0] upstream_bresp;
  logic upstream_bvalid;
  logic upstream_awready;
  logic upstream_wready;
  logic upstream_arready;
  logic [ArAxiIdWidth-1:0] upstream_rid;
  logic [DataWidth-1:0] upstream_rdata;
  logic [RUserWidth-1:0] upstream_ruser;
  logic [AxiRespWidth-1:0] upstream_rresp;
  logic upstream_rlast;
  logic upstream_rvalid;

  logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_awaddr;
  logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_awid;
  logic [NumSubordinates-1:0][AxiBurstLenWidth-1:0] downstream_awlen;
  logic [NumSubordinates-1:0][AxiBurstSizeWidth-1:0] downstream_awsize;
  logic [NumSubordinates-1:0][AxiBurstTypeWidth-1:0] downstream_awburst;
  logic [NumSubordinates-1:0][AxiCacheWidth-1:0] downstream_awcache;
  logic [NumSubordinates-1:0][AxiProtWidth-1:0] downstream_awprot;
  logic [NumSubordinates-1:0][AWUserWidth-1:0] downstream_awuser;
  logic [NumSubordinates-1:0] downstream_awvalid;
  logic [NumSubordinates-1:0][DataWidth-1:0] downstream_wdata;
  logic [NumSubordinates-1:0][StrobeWidth-1:0] downstream_wstrb;
  logic [NumSubordinates-1:0][WUserWidth-1:0] downstream_wuser;
  logic [NumSubordinates-1:0] downstream_wlast;
  logic [NumSubordinates-1:0] downstream_wvalid;
  logic [NumSubordinates-1:0] downstream_bready;
  logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_araddr;
  logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_arid;
  logic [NumSubordinates-1:0][AxiBurstLenWidth-1:0] downstream_arlen;
  logic [NumSubordinates-1:0][AxiBurstSizeWidth-1:0] downstream_arsize;
  logic [NumSubordinates-1:0][AxiBurstTypeWidth-1:0] downstream_arburst;
  logic [NumSubordinates-1:0][AxiCacheWidth-1:0] downstream_arcache;
  logic [NumSubordinates-1:0][AxiProtWidth-1:0] downstream_arprot;
  logic [NumSubordinates-1:0][ARUserWidth-1:0] downstream_aruser;
  logic [NumSubordinates-1:0] downstream_arvalid;
  logic [NumSubordinates-1:0] downstream_rready;

  // Instantiate DUT
  br_amba_axi_demux #(
      .NumSubordinates(NumSubordinates),
      .AwAxiIdWidth(AwAxiIdWidth),
      .ArAxiIdWidth(ArAxiIdWidth),
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth)
  ) dut (
      .clk(clk),
      .rst(rst),
      .upstream_aw_sub_select(upstream_aw_sub_select),
      .upstream_awaddr(upstream_awaddr),
      .upstream_awid(upstream_awid),
      .upstream_awlen(upstream_awlen),
      .upstream_awsize(upstream_awsize),
      .upstream_awburst(upstream_awburst),
      .upstream_awcache(upstream_awcache),
      .upstream_awprot(upstream_awprot),
      .upstream_awuser(upstream_awuser),
      .upstream_awvalid(upstream_awvalid),
      .upstream_awready(upstream_awready),
      .upstream_wdata(upstream_wdata),
      .upstream_wstrb(upstream_wstrb),
      .upstream_wuser(upstream_wuser),
      .upstream_wlast(upstream_wlast),
      .upstream_wvalid(upstream_wvalid),
      .upstream_wready(upstream_wready),
      .upstream_bid(upstream_bid),
      .upstream_buser(upstream_buser),
      .upstream_bresp(upstream_bresp),
      .upstream_bvalid(upstream_bvalid),
      .upstream_bready(upstream_bready),
      .upstream_ar_sub_select(upstream_ar_sub_select),
      .upstream_araddr(upstream_araddr),
      .upstream_arid(upstream_arid),
      .upstream_arlen(upstream_arlen),
      .upstream_arsize(upstream_arsize),
      .upstream_arburst(upstream_arburst),
      .upstream_arcache(upstream_arcache),
      .upstream_arprot(upstream_arprot),
      .upstream_aruser(upstream_aruser),
      .upstream_arvalid(upstream_arvalid),
      .upstream_arready(upstream_arready),
      .upstream_rid(upstream_rid),
      .upstream_rdata(upstream_rdata),
      .upstream_ruser(upstream_ruser),
      .upstream_rresp(upstream_rresp),
      .upstream_rlast(upstream_rlast),
      .upstream_rvalid(upstream_rvalid),
      .upstream_rready(upstream_rready),
      .downstream_awaddr(downstream_awaddr),
      .downstream_awid(downstream_awid),
      .downstream_awlen(downstream_awlen),
      .downstream_awsize(downstream_awsize),
      .downstream_awburst(downstream_awburst),
      .downstream_awcache(downstream_awcache),
      .downstream_awprot(downstream_awprot),
      .downstream_awuser(downstream_awuser),
      .downstream_awvalid(downstream_awvalid),
      .downstream_awready(downstream_awready),
      .downstream_wdata(downstream_wdata),
      .downstream_wstrb(downstream_wstrb),
      .downstream_wuser(downstream_wuser),
      .downstream_wlast(downstream_wlast),
      .downstream_wvalid(downstream_wvalid),
      .downstream_wready(downstream_wready),
      .downstream_bid(downstream_bid),
      .downstream_buser(downstream_buser),
      .downstream_bresp(downstream_bresp),
      .downstream_bvalid(downstream_bvalid),
      .downstream_bready(downstream_bready),
      .downstream_araddr(downstream_araddr),
      .downstream_arid(downstream_arid),
      .downstream_arlen(downstream_arlen),
      .downstream_arsize(downstream_arsize),
      .downstream_arburst(downstream_arburst),
      .downstream_arcache(downstream_arcache),
      .downstream_arprot(downstream_arprot),
      .downstream_aruser(downstream_aruser),
      .downstream_arvalid(downstream_arvalid),
      .downstream_arready(downstream_arready),
      .downstream_rid(downstream_rid),
      .downstream_rdata(downstream_rdata),
      .downstream_ruser(downstream_ruser),
      .downstream_rresp(downstream_rresp),
      .downstream_rlast(downstream_rlast),
      .downstream_rvalid(downstream_rvalid),
      .downstream_rready(downstream_rready)
  );

  // Test sequence
  initial begin
    rst = 1;
    repeat (20) @(posedge clk);
    rst = 0;
    repeat (100) @(posedge clk);
    $display("TEST PASSED");
    $finish;
  end

endmodule
