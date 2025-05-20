// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL AXI Demux

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_demux_fpv_monitor #(
    // Number of downstream subordinates.
    parameter int NumSubordinates = 2,
    // Width of the AXI ID field for the write path.
    parameter int AwAxiIdWidth = 1,
    // Width of the AXI ID field for the read path.
    parameter int ArAxiIdWidth = 1,
    // Maximum number of outstanding write transactions.
    parameter int AwMaxOutstanding = 3,
    // Maximum number of outstanding read transactions.
    parameter int ArMaxOutstanding = 3,
    // If 1, then only a single ID is supported on both the write and read paths.
    parameter int SingleIdOnly = 0,
    // Depth of the write data buffer. This number of WDATA pushes can be buffered
    // before the write address is accepted.
    parameter int WdataBufferDepth = 2,
    // Maximum number of outstanding write transactions that can be accepted before
    // corresponding WDATA pushes are accepted.
    parameter int MaxAwRunahead = 4,
    // Width of the AXI address field.
    parameter int AddrWidth = 12,
    // Width of the AXI data field.
    parameter int DataWidth = 32,
    // Width of the AXI AWUSER field.
    parameter int AWUserWidth = 1,
    // Width of the AXI WUSER field.
    parameter int WUserWidth = 1,
    // Width of the AXI ARUSER field.
    parameter int ARUserWidth = 1,
    // Width of the AXI BUSER field.
    parameter int BUserWidth = 1,
    // Width of the AXI RUSER field.
    parameter int RUserWidth = 1,
    // Number of pipeline stages to use for the pointer RAM read
    // data in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoPointerRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the data RAM read data
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoDataRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the pointer RAM address
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoPointerRamAddressDepthStages = 1,
    // Number of pipeline stages to use for the data RAM address
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoDataRamAddressDepthStages = 1,
    // Number of linked lists per FIFO in the response tracker FIFO. Has
    // no effect if SingleIdOnly == 1.
    parameter int FifoNumLinkedListsPerFifo = 2,
    // Number of pipeline stages to use for the staging buffer
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoStagingBufferDepth = 2,
    // Number of pipeline stages to use for the pop outputs
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoRegisterPopOutputs = 1,
    // Number of pipeline stages to use for the deallocation
    // in the response tracker FIFO. Has no effect if SingleIdOnly == 1.
    parameter int FifoRegisterDeallocation = 1,
    localparam int StrobeWidth = DataWidth / 8,
    localparam int SubIdWidth = $clog2(NumSubordinates)
) (
    input logic clk,
    input logic rst,
    //
    input logic [SubIdWidth-1:0] upstream_aw_sub_select,
    //
    input logic [AddrWidth-1:0] upstream_awaddr,
    input logic [AwAxiIdWidth-1:0] upstream_awid,
    input logic [br_amba::AxiBurstLenWidth-1:0] upstream_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
    input logic [br_amba::AxiCacheWidth-1:0] upstream_awcache,
    input logic [br_amba::AxiProtWidth-1:0] upstream_awprot,
    input logic [AWUserWidth-1:0] upstream_awuser,
    input logic upstream_awvalid,
    input logic upstream_awready,
    input logic [DataWidth-1:0] upstream_wdata,
    input logic [StrobeWidth-1:0] upstream_wstrb,
    input logic [WUserWidth-1:0] upstream_wuser,
    input logic upstream_wlast,
    input logic upstream_wvalid,
    input logic upstream_wready,
    input logic [AwAxiIdWidth-1:0] upstream_bid,
    input logic [BUserWidth-1:0] upstream_buser,
    input logic [br_amba::AxiRespWidth-1:0] upstream_bresp,
    input logic upstream_bvalid,
    input logic upstream_bready,
    //
    input logic [SubIdWidth-1:0] upstream_ar_sub_select,
    //
    input logic [AddrWidth-1:0] upstream_araddr,
    input logic [ArAxiIdWidth-1:0] upstream_arid,
    input logic [br_amba::AxiBurstLenWidth-1:0] upstream_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] upstream_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] upstream_arburst,
    input logic [br_amba::AxiCacheWidth-1:0] upstream_arcache,
    input logic [br_amba::AxiProtWidth-1:0] upstream_arprot,
    input logic [ARUserWidth-1:0] upstream_aruser,
    input logic upstream_arvalid,
    input logic upstream_arready,
    input logic [ArAxiIdWidth-1:0] upstream_rid,
    input logic [DataWidth-1:0] upstream_rdata,
    input logic [RUserWidth-1:0] upstream_ruser,
    input logic [br_amba::AxiRespWidth-1:0] upstream_rresp,
    input logic upstream_rlast,
    input logic upstream_rvalid,
    input logic upstream_rready,
    //
    input logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_awaddr,
    input logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_awid,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstLenWidth-1:0] downstream_awlen,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstSizeWidth-1:0] downstream_awsize,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstTypeWidth-1:0] downstream_awburst,
    input logic [NumSubordinates-1:0][br_amba::AxiCacheWidth-1:0] downstream_awcache,
    input logic [NumSubordinates-1:0][br_amba::AxiProtWidth-1:0] downstream_awprot,
    input logic [NumSubordinates-1:0][AWUserWidth-1:0] downstream_awuser,
    input logic [NumSubordinates-1:0] downstream_awvalid,
    input logic [NumSubordinates-1:0] downstream_awready,
    input logic [NumSubordinates-1:0][DataWidth-1:0] downstream_wdata,
    input logic [NumSubordinates-1:0][StrobeWidth-1:0] downstream_wstrb,
    input logic [NumSubordinates-1:0][WUserWidth-1:0] downstream_wuser,
    input logic [NumSubordinates-1:0] downstream_wlast,
    input logic [NumSubordinates-1:0] downstream_wvalid,
    input logic [NumSubordinates-1:0] downstream_wready,
    input logic [NumSubordinates-1:0][AwAxiIdWidth-1:0] downstream_bid,
    input logic [NumSubordinates-1:0][BUserWidth-1:0] downstream_buser,
    input logic [NumSubordinates-1:0][br_amba::AxiRespWidth-1:0] downstream_bresp,
    input logic [NumSubordinates-1:0] downstream_bvalid,
    input logic [NumSubordinates-1:0] downstream_bready,
    input logic [NumSubordinates-1:0][AddrWidth-1:0] downstream_araddr,
    input logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_arid,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstLenWidth-1:0] downstream_arlen,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstSizeWidth-1:0] downstream_arsize,
    input logic [NumSubordinates-1:0][br_amba::AxiBurstTypeWidth-1:0] downstream_arburst,
    input logic [NumSubordinates-1:0][br_amba::AxiCacheWidth-1:0] downstream_arcache,
    input logic [NumSubordinates-1:0][br_amba::AxiProtWidth-1:0] downstream_arprot,
    input logic [NumSubordinates-1:0][ARUserWidth-1:0] downstream_aruser,
    input logic [NumSubordinates-1:0] downstream_arvalid,
    input logic [NumSubordinates-1:0] downstream_arready,
    input logic [NumSubordinates-1:0][ArAxiIdWidth-1:0] downstream_rid,
    input logic [NumSubordinates-1:0][DataWidth-1:0] downstream_rdata,
    input logic [NumSubordinates-1:0][RUserWidth-1:0] downstream_ruser,
    input logic [NumSubordinates-1:0][br_amba::AxiRespWidth-1:0] downstream_rresp,
    input logic [NumSubordinates-1:0] downstream_rlast,
    input logic [NumSubordinates-1:0] downstream_rvalid,
    input logic [NumSubordinates-1:0] downstream_rready
);

  // TODO: FV MAX_PENDING_RD, MAX_PENDING_WR should be bigger than RTL to test backpressure
  // MAX_PENDING_WR shiuld be MaxAwRunahead + 1
  // MAX_PENDING_RD should be ArMaxOutstanding + 1
  `BR_ASSUME(aw_legal_awid_a, upstream_awid < AwMaxOutstanding)
  `BR_ASSUME(ar_legal_arid_a, upstream_arid < ArMaxOutstanding)
  `BR_ASSUME(aw_legal_subId_a, upstream_aw_sub_select < NumSubordinates)
  `BR_ASSUME(ar_legal_subId_a, upstream_ar_sub_select < NumSubordinates)

  // track awid, arid going to which subordinate
  logic [AwAxiIdWidth-1:0] upstream_wid;  // create wid to tag transactions
  // w_buffer signals
  logic w_buffer_empty;
  logic w_buffer_push;
  logic w_buffer_pop;
  logic [AwAxiIdWidth-1:0] w_buffer_wid;
  // aw_buffer signals
  logic aw_buffer_empty;
  logic [AwAxiIdWidth-1:0] aw_buffer_awid;
  // pop both buffer together
  logic buffer_pop;
  // w_cntr tracks number of wvalids associated with a awvalid
  logic [br_amba::AxiBurstLenWidth:0] w_cntr;
  logic [AwMaxOutstanding-1:0][SubIdWidth:0] w_sub_id;
  logic [AwMaxOutstanding-1:0][SubIdWidth:0] b_sub_id;
  logic [ArMaxOutstanding-1:0][SubIdWidth:0] r_sub_id;
  logic same_cyc_aw_w;
  logic same_cyc_ar_r;

  assign buffer_pop = !w_buffer_empty && !aw_buffer_empty;

  // RTL can accept WdataBufferDepth of wdata without awvalid
  fv_fifo #(
      .Depth(WdataBufferDepth),
      .DataWidth(AwAxiIdWidth),
      .Bypass(1)
  ) w_buffer (
      .clk(clk),
      .rst(rst),
      .push(upstream_wvalid & upstream_wready & upstream_wlast),
      .push_data(upstream_wid),
      .pop(buffer_pop),
      .pop_data(w_buffer_wid),
      .empty(w_buffer_empty),
      .full()
  );

  // RTL can accept MaxAwRunahead of awid without wvalid
  fv_fifo #(
      .Depth(MaxAwRunahead),
      .DataWidth(AwAxiIdWidth),
      .Bypass(1)
  ) aw_buffer (
      .clk(clk),
      .rst(rst),
      .push(upstream_awvalid & upstream_awready),
      .push_data(upstream_awid),
      .pop(buffer_pop),
      .pop_data(aw_buffer_awid),
      .empty(aw_buffer_empty),
      .full()
  );

  `BR_ASSUME(create_upstream_awid_a, w_buffer_wid == aw_buffer_awid)

  // create subordinate id for w,b,r
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < AwMaxOutstanding; i++) begin
        w_sub_id[i] <= NumSubordinates;  // set to an impossible value
      end
    end else begin
      // TODO: bug. if w came bafore aw, this doesn't work
      if (upstream_awvalid) begin
        w_sub_id[upstream_awid] <= upstream_aw_sub_select;
      end
      if (upstream_wvalid & upstream_wlast) begin
        w_sub_id[upstream_wid] <= NumSubordinates;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < AwMaxOutstanding; i++) begin
        b_sub_id[i] <= NumSubordinates;  // set to an impossible value
      end
    end else if (upstream_awvalid) begin
      b_sub_id[upstream_awid] <= upstream_aw_sub_select;
    end else if (upstream_bvalid) begin
      b_sub_id[upstream_bid] <= NumSubordinates;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < ArMaxOutstanding; i++) begin
        r_sub_id[i] <= NumSubordinates;  // set to an impossible value
      end
    end else if (upstream_arvalid) begin
      r_sub_id[upstream_arid] <= upstream_ar_sub_select;
    end else if (upstream_rvalid & upstream_rlast) begin
      r_sub_id[upstream_rid] <= NumSubordinates;
    end
  end

  assign same_cyc_ar_r = (upstream_arvalid && upstream_rvalid && (upstream_arid == upstream_rid));
  assign same_cyc_aw_w = (upstream_awvalid && upstream_wvalid && (upstream_awid == upstream_wid));

  // upstream itself should also be AXI compliant
  axi4_master #(
      .ID_WIDTH_W(AwAxiIdWidth),
      .ID_WIDTH_R(ArAxiIdWidth),
      .ADDR_WIDTH(AddrWidth),
      .LEN_WIDTH(br_amba::AxiBurstLenWidth),
      .SIZE_WIDTH(br_amba::AxiBurstSizeWidth),
      .BURST_WIDTH(br_amba::AxiBurstTypeWidth),
      .PROT_WIDTH(br_amba::AxiProtWidth),
      .CACHE_WIDTH(br_amba::AxiCacheWidth),
      .DATA_WIDTH(DataWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .BRESP_WIDTH(br_amba::AxiRespWidth),
      .MAX_PENDING_RD(ArMaxOutstanding),
      .MAX_PENDING_WR(AwMaxOutstanding),
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0),
      .READ_INTERLEAVE_ON(0),
      .DATA_BEFORE_CONTROL_ON(0)  //TODO [temp, need to fix]: turn off "w can come before AW"
  ) upstream (
      // Global signals
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq ('d1),
      .csysack ('d1),
      .cactive ('d1),
      // Write Address Channel
      .awvalid (upstream_awvalid),
      .awready (upstream_awready),
      .awid    (upstream_awid),
      .awaddr  (upstream_awaddr),
      .awlen   (upstream_awlen),
      .awsize  (upstream_awsize),
      .awburst (upstream_awburst),
      .awuser  (upstream_awuser),
      .awprot  (upstream_awprot),
      .awlock  (),
      .awcache (upstream_awcache),
      .awqos   (),
      .awregion(),
      // Write Channel
      .wvalid  (upstream_wvalid),
      .wready  (upstream_wready),
      .wdata   (upstream_wdata),
      .wstrb   (upstream_wstrb),
      .wlast   (upstream_wlast),
      .wuser   (upstream_wuser),
      // Write Response channel
      .bvalid  (upstream_bvalid),
      .bready  (upstream_bready),
      .bid     (upstream_bid),
      .bresp   (upstream_bresp),
      .buser   (upstream_buser),
      // Read Address Channel
      .arvalid (upstream_arvalid),
      .arready (upstream_arready),
      .arid    (upstream_arid),
      .araddr  (upstream_araddr),
      .arlen   (upstream_arlen),
      .arsize  (upstream_arsize),
      .arburst (upstream_arburst),
      .aruser  (upstream_aruser),
      .arprot  (upstream_arprot),
      .arlock  (),
      .arcache (upstream_arcache),
      .arqos   (),
      .arregion(),
      // Read Channel
      .rvalid  (upstream_rvalid),
      .rready  (upstream_rready),
      .ruser   (upstream_ruser),
      .rid     (upstream_rid),
      .rdata   (upstream_rdata),
      .rresp   (upstream_rresp),
      .rlast   (upstream_rlast)
  );

  // for each upstream and downstream pair, they should be AXI compliant
  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_pair
    up_down_fv_check #(
        .AwAxiIdWidth(AwAxiIdWidth),
        .ArAxiIdWidth(ArAxiIdWidth),
        .AwMaxOutstanding(AwMaxOutstanding),
        .ArMaxOutstanding(ArMaxOutstanding),
        .SingleIdOnly(SingleIdOnly),
        .WdataBufferDepth(WdataBufferDepth),
        .MaxAwRunahead(MaxAwRunahead),
        .AddrWidth(AddrWidth),
        .DataWidth(DataWidth),
        .AWUserWidth(AWUserWidth),
        .WUserWidth(WUserWidth),
        .ARUserWidth(ARUserWidth),
        .BUserWidth(BUserWidth),
        .RUserWidth(RUserWidth)
    ) up_down_pair (
        .clk,
        .rst,
        // aw
        .upstream_awaddr,
        .upstream_awid,
        .upstream_awlen,
        .upstream_awsize,
        .upstream_awburst,
        .upstream_awcache,
        .upstream_awprot,
        .upstream_awuser,
        .upstream_awvalid(upstream_awvalid && (upstream_aw_sub_select == i)),
        .upstream_awready,
        // w
        .upstream_wdata,
        .upstream_wstrb,
        .upstream_wuser,
        .upstream_wlast,
        .upstream_wvalid(upstream_wvalid &&
                        (same_cyc_aw_w ? (upstream_aw_sub_select == i) :
                        w_sub_id[upstream_wid] == i)),
        .upstream_wready,
        // b
        .upstream_bid,
        .upstream_buser,
        .upstream_bresp,
        .upstream_bvalid(upstream_bvalid && (b_sub_id[upstream_bid] == i)),
        .upstream_bready,
        // ar
        .upstream_araddr,
        .upstream_arid,
        .upstream_arlen,
        .upstream_arsize,
        .upstream_arburst,
        .upstream_arcache,
        .upstream_arprot,
        .upstream_aruser,
        .upstream_arvalid(upstream_arvalid && (upstream_ar_sub_select == i)),
        .upstream_arready,
        // r
        .upstream_rid,
        .upstream_rdata,
        .upstream_ruser,
        .upstream_rresp,
        .upstream_rlast,
        .upstream_rvalid(upstream_rvalid &&
                        (same_cyc_ar_r ? (upstream_ar_sub_select == i) :
                        r_sub_id[upstream_rid] == i)),
        .upstream_rready,
        // downstream
        .downstream_awaddr(downstream_awaddr[i]),
        .downstream_awid(downstream_awid[i]),
        .downstream_awlen(downstream_awlen[i]),
        .downstream_awsize(downstream_awsize[i]),
        .downstream_awburst(downstream_awburst[i]),
        .downstream_awcache(downstream_awcache[i]),
        .downstream_awprot(downstream_awprot[i]),
        .downstream_awuser(downstream_awuser[i]),
        .downstream_awvalid(downstream_awvalid[i]),
        .downstream_awready(downstream_awready[i]),
        .downstream_wdata(downstream_wdata[i]),
        .downstream_wstrb(downstream_wstrb[i]),
        .downstream_wuser(downstream_wuser[i]),
        .downstream_wlast(downstream_wlast[i]),
        .downstream_wvalid(downstream_wvalid[i]),
        .downstream_wready(downstream_wready[i]),
        .downstream_bid(downstream_bid[i]),
        .downstream_buser(downstream_buser[i]),
        .downstream_bresp(downstream_bresp[i]),
        .downstream_bvalid(downstream_bvalid[i]),
        .downstream_bready(downstream_bready[i]),
        .downstream_araddr(downstream_araddr[i]),
        .downstream_arid(downstream_arid[i]),
        .downstream_arlen(downstream_arlen[i]),
        .downstream_arsize(downstream_arsize[i]),
        .downstream_arburst(downstream_arburst[i]),
        .downstream_arcache(downstream_arcache[i]),
        .downstream_arprot(downstream_arprot[i]),
        .downstream_aruser(downstream_aruser[i]),
        .downstream_arvalid(downstream_arvalid[i]),
        .downstream_arready(downstream_arready[i]),
        .downstream_rid(downstream_rid[i]),
        .downstream_rdata(downstream_rdata[i]),
        .downstream_ruser(downstream_ruser[i]),
        .downstream_rresp(downstream_rresp[i]),
        .downstream_rlast(downstream_rlast[i]),
        .downstream_rvalid(downstream_rvalid[i]),
        .downstream_rready(downstream_rready[i])
    );
  end

endmodule : br_amba_axi_demux_fpv_monitor

bind br_amba_axi_demux br_amba_axi_demux_fpv_monitor #(
    .NumSubordinates(NumSubordinates),
    .AwAxiIdWidth(AwAxiIdWidth),
    .ArAxiIdWidth(ArAxiIdWidth),
    .AwMaxOutstanding(AwMaxOutstanding),
    .ArMaxOutstanding(ArMaxOutstanding),
    .SingleIdOnly(SingleIdOnly),
    .WdataBufferDepth(WdataBufferDepth),
    .MaxAwRunahead(MaxAwRunahead),
    .AddrWidth(AddrWidth),
    .DataWidth(DataWidth),
    .AWUserWidth(AWUserWidth),
    .WUserWidth(WUserWidth),
    .ARUserWidth(ARUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .FifoPointerRamReadDataDepthStages(FifoPointerRamReadDataDepthStages),
    .FifoDataRamReadDataDepthStages(FifoDataRamReadDataDepthStages),
    .FifoPointerRamAddressDepthStages(FifoPointerRamAddressDepthStages),
    .FifoDataRamAddressDepthStages(FifoDataRamAddressDepthStages),
    .FifoNumLinkedListsPerFifo(FifoNumLinkedListsPerFifo),
    .FifoStagingBufferDepth(FifoStagingBufferDepth),
    .FifoRegisterPopOutputs(FifoRegisterPopOutputs),
    .FifoRegisterDeallocation(FifoRegisterDeallocation)
) monitor (.*);
