`timescale 1ns / 1ps

module br_amba_axi_isolate_sub_tb;

  logic clk = 0;
  logic rst = 1;

  // Clock generation
  always #5 clk = ~clk;

  // Instantiate DUT with direct tie-offs
  br_amba_axi_isolate_sub dut (
      .clk(clk),
      .rst(rst),
      .isolate_req(1'b0),
      .isolate_done(),
      .upstream_awaddr('0),
      .upstream_awid('0),
      .upstream_awlen('0),
      .upstream_awsize('0),
      .upstream_awburst('0),
      .upstream_awcache('0),
      .upstream_awprot('0),
      .upstream_awuser('0),
      .upstream_awvalid(1'b0),
      .upstream_awready(),
      .upstream_wdata('0),
      .upstream_wstrb('0),
      .upstream_wuser('0),
      .upstream_wlast(1'b0),
      .upstream_wvalid(1'b0),
      .upstream_wready(),
      .upstream_bid(),
      .upstream_buser(),
      .upstream_bresp(),
      .upstream_bvalid(),
      .upstream_bready(1'b0),
      .upstream_araddr('0),
      .upstream_arid('0),
      .upstream_arlen('0),
      .upstream_arsize('0),
      .upstream_arburst('0),
      .upstream_arcache('0),
      .upstream_arprot('0),
      .upstream_aruser('0),
      .upstream_arvalid(1'b0),
      .upstream_arready(),
      .upstream_rid(),
      .upstream_rdata(),
      .upstream_ruser(),
      .upstream_rresp(),
      .upstream_rlast(),
      .upstream_rvalid(),
      .upstream_rready(1'b0),
      .downstream_awaddr(),
      .downstream_awid(),
      .downstream_awlen(),
      .downstream_awsize(),
      .downstream_awburst(),
      .downstream_awcache(),
      .downstream_awprot(),
      .downstream_awuser(),
      .downstream_awvalid(),
      .downstream_awready(1'b0),
      .downstream_wdata(),
      .downstream_wstrb(),
      .downstream_wuser(),
      .downstream_wlast(),
      .downstream_wvalid(),
      .downstream_wready(1'b0),
      .downstream_bid('0),
      .downstream_buser('0),
      .downstream_bresp('0),
      .downstream_bvalid(1'b0),
      .downstream_bready(),
      .downstream_araddr(),
      .downstream_arid(),
      .downstream_arlen(),
      .downstream_arsize(),
      .downstream_arburst(),
      .downstream_arcache(),
      .downstream_arprot(),
      .downstream_aruser(),
      .downstream_arvalid(),
      .downstream_arready(1'b0),
      .downstream_rid('0),
      .downstream_rdata('0),
      .downstream_ruser('0),
      .downstream_rresp('0),
      .downstream_rlast(1'b0),
      .downstream_rvalid(1'b0),
      .downstream_rready()
  );

  // Test sequence
  initial begin
    rst = 1;
    repeat (20) @(posedge clk);
    @(negedge clk);
    rst = 0;
    repeat (100) @(posedge clk);
    $display("TEST PASSED");
    $finish;
  end

endmodule
