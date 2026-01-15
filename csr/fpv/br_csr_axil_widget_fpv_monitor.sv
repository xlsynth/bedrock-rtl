// SPDX-License-Identifier: Apache-2.0
// Bedrock-RTL AXI4-Lite to SCB Widget FV Monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_csr_axil_widget_fpv_monitor #(
    parameter int AddrWidth = 1,
    parameter int DataWidth = 32,
    parameter bit RegisterResponseOutputs = 0,
    parameter int MaxTimeoutCycles = 1000,
    localparam int StrobeWidth = DataWidth / 8,
    localparam int TimerWidth = br_math::clamped_clog2(MaxTimeoutCycles + 1)
) (
    input logic clk,
    input logic rst,

    // AXI4-Lite target interface
    input logic                             axil_awvalid,
    input logic                             axil_awready,
    input logic [            AddrWidth-1:0] axil_awaddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_awprot,
    input logic                             axil_wvalid,
    input logic                             axil_wready,
    input logic [            DataWidth-1:0] axil_wdata,
    input logic [          StrobeWidth-1:0] axil_wstrb,
    input logic                             axil_bvalid,
    input logic                             axil_bready,
    input logic [br_amba::AxiRespWidth-1:0] axil_bresp,
    input logic                             axil_arvalid,
    input logic                             axil_arready,
    input logic [            AddrWidth-1:0] axil_araddr,
    input logic [br_amba::AxiProtWidth-1:0] axil_arprot,
    input logic                             axil_rvalid,
    input logic                             axil_rready,
    input logic [            DataWidth-1:0] axil_rdata,
    input logic [br_amba::AxiRespWidth-1:0] axil_rresp,

    input logic                   csr_req_valid,
    // 1 indicates a write request, 0 indicates a read request
    input logic                   csr_req_write,
    input logic [  AddrWidth-1:0] csr_req_addr,
    input logic [  DataWidth-1:0] csr_req_wdata,
    input logic [StrobeWidth-1:0] csr_req_wstrb,
    input logic                   csr_req_secure,
    input logic                   csr_req_privileged,
    input logic                   csr_req_abort,

    input logic                 csr_resp_valid,
    input logic [DataWidth-1:0] csr_resp_rdata,
    input logic                 csr_resp_slverr,
    input logic                 csr_resp_decerr,

    input logic [TimerWidth-1:0] timeout_cycles,
    input logic                  request_aborted
);

  // AXI4-Lite interface
  axi4_master #(
      .AXI4_LITE(1),
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(DataWidth),
      // when there is no valid, ready doesn't have to be high eventually
      // This will only turn off assertion without precondition: `STRENGTH(##[0:$] arready
      // (arvalid && !arready) |=> `STRENGTH(##[0:$] arready) is still enabled
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .MAX_PENDING(RegisterResponseOutputs ? 3 : 2)
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
      .awaddr  (axil_awaddr),
      .awprot  (axil_awprot),
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
      .wvalid  (axil_wvalid),
      .wready  (axil_wready),
      .wdata   (axil_wdata),
      .wstrb   (axil_wstrb),
      .wuser   (),
      .wlast   (),
      // Write Response channel
      .bvalid  (axil_bvalid),
      .bready  (axil_bready),
      .bresp   (axil_bresp),
      .bid     (),
      .buser   (),
      // Read Address Channel
      .arvalid (axil_arvalid),
      .arready (axil_arready),
      .araddr  (axil_araddr),
      .arprot  (axil_arprot),
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
      .rvalid  (axil_rvalid),
      .rready  (axil_rready),
      .rdata   (axil_rdata),
      .rresp   (axil_rresp),
      .ruser   (),
      .rid     (),
      .rlast   ()
  );

  // ----------FV Modeling Code----------
  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic secure;
    logic privileged;
  } araw_req_t;

  typedef struct packed {
    logic [DataWidth-1:0]   wdata;
    logic [StrobeWidth-1:0] wstrb;
  } w_t;

  logic csr_req_pending;
  logic csr_write_req_pending;
  logic csr_req_aborting;
  araw_req_t csr_write_req, csr_read_req;
  w_t csr_write_data;
  logic [br_amba::AxiRespWidth-1:0] csr_resp;
  logic [TimerWidth:0] timer;
  logic timer_expired;

  always_ff @(posedge clk) begin
    if (rst) begin
      csr_req_pending <= 1'b0;
      csr_write_req_pending <= 1'b0;
    end else if (csr_req_valid) begin
      csr_req_pending <= 1'b1;
      csr_write_req_pending <= csr_req_write;
    end else if (csr_resp_valid || request_aborted) begin
      csr_req_pending <= 1'b0;
      csr_write_req_pending <= 1'b0;
    end
  end

  // when first period expired, csr_req_abort is sent.
  // within timeout_cycles cycles, if no response is received, request is aborted.
  always_ff @(posedge clk) begin
    if (rst) begin
      csr_req_aborting <= 1'b0;
    end else if (csr_req_abort) begin
      csr_req_aborting <= 1'b1;
    end else if (csr_resp_valid || request_aborted) begin
      csr_req_aborting <= 1'b0;
    end
  end

  // when first period expired, csr_req_abort is sent.
  // The timer will then reset and count for another timeout period.
  // If no response is received before the second period expires, request_aborted is set.
  always_ff @(posedge clk) begin
    if (rst | csr_req_abort | csr_resp_valid | request_aborted) begin
      timer <= 1'b0;
    end else if (csr_write_req_pending) begin
      timer <= timer + 1'b1;
    end
  end
  assign timer_expired = (timer >= timeout_cycles);

  assign csr_write_req = '{
          addr: axil_awaddr,
          secure: !axil_awprot[1],
          privileged: axil_awprot[0]
      };

  assign csr_read_req = '{
          addr: axil_araddr,
          secure: !axil_arprot[1],
          privileged: axil_arprot[0]
      };

  assign csr_write_data = '{wdata: axil_wdata, wstrb: axil_wstrb};

  // - axil_rresp <- 11 if csr_resp_decerr=1, 10 if csr_resp_slverr=1, 00 if neither are set
  assign csr_resp = csr_resp_decerr ? 2'b11 : csr_resp_slverr ? 2'b10 : 2'b00;

  // ----------FV assumptions----------
  // TODO(masai): https://github.com/xlsynth/bedrock-rtl/issues/955
  `BR_ASSUME(timeout_cycles_non_zero_a, timeout_cycles != 'd0)
  `BR_ASSUME(legal_timeout_cycles_a, timeout_cycles <= MaxTimeoutCycles)
  `BR_ASSUME(legal_csr_resp_a, csr_resp_valid |-> !(csr_resp_decerr && csr_resp_slverr))
  `BR_ASSUME(no_spurious_csr_req_resp_a, !csr_req_pending |-> !csr_resp_valid);
  `BR_ASSUME(eventually_csr_req_resp_a, csr_req_pending |-> s_eventually csr_resp_valid);

  // ----------FV assertions----------
  `BR_ASSERT(only_one_outstanding_csr_req_a, csr_req_pending |-> !csr_req_valid);
  `BR_ASSERT(no_deadlock_aw_a, axil_awvalid |-> s_eventually csr_req_valid && csr_req_write);
  `BR_ASSERT(no_deadlock_w_a, axil_wvalid |-> s_eventually csr_req_valid && csr_req_write);
  `BR_ASSERT(no_deadlock_ar_a, axil_arvalid |-> s_eventually csr_req_valid && !csr_req_write);
  `BR_ASSERT(no_deadlock_b_a, csr_resp_valid && csr_write_req_pending |-> s_eventually axil_bvalid);
  `BR_ASSERT(no_deadlock_r_a,
             csr_resp_valid && !csr_write_req_pending |-> s_eventually axil_rvalid);
  `BR_ASSERT(
      csr_req_1st_timeout_a,
      csr_req_pending && !csr_req_aborting && timer_expired && !csr_resp_valid |-> csr_req_abort);
  `BR_ASSERT(
      csr_req_2nd_timeout_a,
      csr_req_pending && csr_req_aborting && timer_expired && !csr_resp_valid |-> request_aborted);

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH($bits(araw_req_t)),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) aw_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(axil_awvalid & axil_awready),
      .incoming_data(csr_write_req),
      .outgoing_vld(csr_req_valid & csr_req_write),
      .outgoing_data({csr_req_addr, csr_req_secure, csr_req_privileged})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH($bits(w_t)),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) w_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(axil_wvalid & axil_wready),
      .incoming_data(csr_write_data),
      .outgoing_vld(csr_req_valid & csr_req_write),
      .outgoing_data({csr_req_wdata, csr_req_wstrb})
  );

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH($bits(araw_req_t)),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) ar_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(axil_arvalid & axil_arready),
      .incoming_data(csr_read_req),
      .outgoing_vld(csr_req_valid & !csr_req_write),
      .outgoing_data({csr_req_addr, csr_req_secure, csr_req_privileged})
  );

  // If no response is received before the second period expires,
  // a response with code SLVERR is sent on the AXI B channel for write.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(br_amba::AxiRespWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) b_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld((csr_resp_valid | request_aborted) & csr_write_req_pending),
      .incoming_data(request_aborted ? 2'b10 : csr_resp),
      .outgoing_vld(axil_bvalid & axil_bready),
      .outgoing_data(axil_bresp)
  );

  // If no response is received before the second period expires,
  // a response with code SLVERR is sent on the AXI R channel for read.
  // axil_rdata is zeroed out in this case.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(br_amba::AxiRespWidth + DataWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) r_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld((csr_resp_valid | request_aborted) & !csr_write_req_pending),
      .incoming_data(request_aborted ? {2'b10, {DataWidth{1'b0}}} : {csr_resp, csr_resp_rdata}),
      .outgoing_vld(axil_rvalid & axil_rready),
      .outgoing_data({axil_rresp, axil_rdata})
  );

endmodule : br_csr_axil_widget_fpv_monitor

bind br_csr_axil_widget br_csr_axil_widget_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .RegisterResponseOutputs(RegisterResponseOutputs),
    .MaxTimeoutCycles(MaxTimeoutCycles)
) monitor (.*);
