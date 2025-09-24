// SPDX-License-Identifier: Apache-2.0


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
    // Maximum number of outstanding write transactions per ID.
    parameter int AwMaxOutstandingPerId = 3,
    // Maximum number of outstanding read transactions per ID.
    parameter int ArMaxOutstandingPerId = 3,
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

  typedef struct packed {
    logic [AddrWidth-1:0] awaddr;
    logic [AwAxiIdWidth-1:0] awid;
    logic [br_amba::AxiBurstLenWidth-1:0] awlen;
    logic [br_amba::AxiBurstSizeWidth-1:0] awsize;
    logic [br_amba::AxiBurstTypeWidth-1:0] awburst;
    logic [br_amba::AxiCacheWidth-1:0] awcache;
    logic [br_amba::AxiProtWidth-1:0] awprot;
    logic [AWUserWidth-1:0] awuser;
  } aw_payload_t;

  typedef struct packed {
    logic [AddrWidth-1:0] araddr;
    logic [ArAxiIdWidth-1:0] arid;
    logic [br_amba::AxiBurstLenWidth-1:0] arlen;
    logic [br_amba::AxiBurstSizeWidth-1:0] arsize;
    logic [br_amba::AxiBurstTypeWidth-1:0] arburst;
    logic [br_amba::AxiCacheWidth-1:0] arcache;
    logic [br_amba::AxiProtWidth-1:0] arprot;
    logic [ARUserWidth-1:0] aruser;
  } ar_payload_t;

  typedef struct packed {
    logic [DataWidth-1:0] wdata;
    logic [StrobeWidth-1:0] wstrb;
    logic [WUserWidth-1:0] wuser;
    logic wlast;
  } w_payload_t;

  typedef struct packed {
    logic [AwAxiIdWidth-1:0] upstream_bid;
    logic [BUserWidth-1:0] upstream_buser;
    logic [br_amba::AxiRespWidth-1:0] upstream_bresp;
  } b_payload_t;

  typedef struct packed {
    logic [DataWidth-1:0] rdata;
    logic [RUserWidth-1:0] ruser;
    logic [ArAxiIdWidth-1:0] rid;
    logic [br_amba::AxiRespWidth-1:0] rresp;
    logic rlast;
  } r_payload_t;

  localparam int AwPayloadWidth = $bits(aw_payload_t);
  localparam int ArPayloadWidth = $bits(ar_payload_t);
  localparam int WPayloadWidth = $bits(w_payload_t);
  localparam int BPayloadWidth = $bits(b_payload_t);
  localparam int RPayloadWidth = $bits(r_payload_t);
  // overall MaxOutstanding
  localparam int NumAwId = SingleIdOnly ? 1 : (2 << AwAxiIdWidth);
  localparam int NumArId = SingleIdOnly ? 1 : (2 << ArAxiIdWidth);
  // usually +2 to allow ABVIP to send a few more to test backpressure
  // +2 here to give a few extra slots since DUT has some margin before de-assert ready signal
  localparam int MaxPendingWr = (NumAwId * AwMaxOutstandingPerId) + 2;
  localparam int MaxPendingRd = (NumArId * ArMaxOutstandingPerId) + 2;
  localparam int AwCntrWidth = $clog2(MaxPendingWr);
  localparam int ArCntrWidth = $clog2(MaxPendingRd);

  // if SingleIdOnly = 1, read and write can only use ID = 0
  if (SingleIdOnly) begin : gen_singleId
    `BR_ASSUME(aw_singleidonly_a, upstream_awvalid |-> upstream_awid == 'd0)
    `BR_ASSUME(ar_singleidonly_a, upstream_arvalid |-> upstream_arid == 'd0)
  end

  // pick a random subordinate for checkers
  logic [SubIdWidth-1:0] fv_aw_select;
  logic [SubIdWidth-1:0] fv_ar_select;
  `BR_ASSUME(fv_aw_select_a, $stable(fv_aw_select) && (fv_aw_select < NumSubordinates))
  `BR_ASSUME(fv_ar_select_a, $stable(fv_ar_select) && (fv_ar_select < NumSubordinates))

  `BR_ASSUME(aw_legal_subId_a, upstream_aw_sub_select < NumSubordinates)
  `BR_ASSUME(ar_legal_subId_a, upstream_ar_sub_select < NumSubordinates)
  // aw/ar select should be stable when upstream is not ready
  `BR_ASSUME(aw_select_stable_a, upstream_awvalid && !upstream_awready |=> $stable
                                 (upstream_aw_sub_select))
  `BR_ASSUME(ar_select_stable_a, upstream_arvalid && !upstream_arready |=> $stable
                                 (upstream_ar_sub_select))


  // for each Id, the number of outstanding transactions should be <= MaxOutstandingPerId
  logic [NumAwId-1:0][AwCntrWidth-1:0] AwCntr;
  logic [NumArId-1:0][ArCntrWidth-1:0] ArCntr;

  for (genvar i = 0; i < NumAwId; i++) begin : gen_aw
    `BR_REG(AwCntr[i],
            AwCntr[i] +
            (upstream_awvalid && upstream_awready && (upstream_awid == i)) -
            (upstream_bvalid && upstream_bready && (upstream_bid == i)))
    `BR_ASSUME(max_aw_perId_a, AwCntr[i] <= AwMaxOutstandingPerId)
  end

  for (genvar i = 0; i < NumArId; i++) begin : gen_ar
    `BR_REG(ArCntr[i],
            ArCntr[i] +
            (upstream_arvalid && upstream_arready && (upstream_arid == i)) -
            (upstream_rvalid && upstream_rready && upstream_rlast && (upstream_rid == i)))
    `BR_ASSUME(max_ar_perId_a, ArCntr[i] <= ArMaxOutstandingPerId)
  end

  // If upstream can send correct Aw/Ar traffic to correponding downstream,
  // ABVIP will guarantee W, B, R channels behave correctly.
  aw_payload_t upstream_awPayload;
  ar_payload_t upstream_arPayload;
  w_payload_t upstream_wPayload;
  b_payload_t upstream_bPayload;
  r_payload_t upstream_rPayload;

  aw_payload_t downstream_awPayload;
  ar_payload_t downstream_arPayload;
  w_payload_t [NumSubordinates-1:0] downstream_wPayload;
  b_payload_t [NumSubordinates-1:0] downstream_bPayload;
  r_payload_t [NumSubordinates-1:0] downstream_rPayload;

  assign upstream_awPayload = {
    upstream_awaddr,
    upstream_awid,
    upstream_awlen,
    upstream_awsize,
    upstream_awburst,
    upstream_awcache,
    upstream_awprot,
    upstream_awuser
  };

  assign upstream_wPayload = {upstream_wdata, upstream_wstrb, upstream_wuser, upstream_wlast};

  assign upstream_bPayload = {upstream_bid, upstream_buser, upstream_bresp};

  assign upstream_rPayload = {
    upstream_rdata, upstream_ruser, upstream_rid, upstream_rresp, upstream_rlast
  };

  assign upstream_arPayload = {
    upstream_araddr,
    upstream_arid,
    upstream_arlen,
    upstream_arsize,
    upstream_arburst,
    upstream_arcache,
    upstream_arprot,
    upstream_aruser
  };

  assign downstream_awPayload = {
    downstream_awaddr[fv_aw_select],
    downstream_awid[fv_aw_select],
    downstream_awlen[fv_aw_select],
    downstream_awsize[fv_aw_select],
    downstream_awburst[fv_aw_select],
    downstream_awcache[fv_aw_select],
    downstream_awprot[fv_aw_select],
    downstream_awuser[fv_aw_select]
  };

  assign downstream_arPayload = {
    downstream_araddr[fv_ar_select],
    downstream_arid[fv_ar_select],
    downstream_arlen[fv_ar_select],
    downstream_arsize[fv_ar_select],
    downstream_arburst[fv_ar_select],
    downstream_arcache[fv_ar_select],
    downstream_arprot[fv_ar_select],
    downstream_aruser[fv_ar_select]
  };

  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_payload
    assign downstream_wPayload[i] = {
      downstream_wdata[i], downstream_wstrb[i], downstream_wuser[i], downstream_wlast[i]
    };
    assign downstream_bPayload[i] = {downstream_bid[i], downstream_buser[i], downstream_bresp[i]};
    assign downstream_rPayload[i] = {
      downstream_rdata[i],
      downstream_ruser[i],
      downstream_rid[i],
      downstream_rresp[i],
      downstream_rlast[i]
    };
  end

  // ----------Aw----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AwPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingWr)
  ) aw_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(upstream_awvalid && upstream_awready &&
                    (upstream_aw_sub_select == fv_aw_select)),
      .incoming_data(upstream_awPayload),
      .outgoing_vld(downstream_awvalid[fv_aw_select] & downstream_awready[fv_aw_select]),
      .outgoing_data(downstream_awPayload)
  );

  // ----------Ar----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ArPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingRd)
  ) ar_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(upstream_arvalid && upstream_arready &&
                      (upstream_ar_sub_select == fv_ar_select)),
      .incoming_data(upstream_arPayload),
      .outgoing_vld(downstream_arvalid[fv_ar_select] & downstream_arready[fv_ar_select]),
      .outgoing_data(downstream_arPayload)
  );

  // ----------W data integrity----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(WPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(NumSubordinates),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingWr),
      .ORDERING(`JS3_OUT_OF_ORDER)
  ) w_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(upstream_wvalid && upstream_wready),
      .incoming_data(upstream_wPayload),
      .outgoing_vld(downstream_wvalid & downstream_wready),
      .outgoing_data(downstream_wPayload)
  );
  // ----------B data integrity----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(BPayloadWidth),
      .IN_CHUNKS(NumSubordinates),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingWr),
      .ORDERING(`JS3_OUT_OF_ORDER)
  ) b_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(downstream_bvalid & downstream_bready),
      .incoming_data(downstream_bPayload),
      .outgoing_vld(upstream_bvalid && upstream_bready),
      .outgoing_data(upstream_bPayload)
  );

  // ----------R data integrity----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(RPayloadWidth),
      .IN_CHUNKS(NumSubordinates),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxPendingRd),
      .ORDERING(`JS3_OUT_OF_ORDER)
  ) r_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(downstream_rvalid & downstream_rready),
      .incoming_data(downstream_rPayload),
      .outgoing_vld(upstream_rvalid && upstream_rready),
      .outgoing_data(upstream_rPayload)
  );

  // upstream itself should also be AXI compliants
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
      .MAX_PENDING_RD(MaxPendingRd),
      .MAX_PENDING_WR(MaxPendingWr),
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0),
      .READ_INTERLEAVE_ON(0),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1)
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
  for (genvar i = 0; i < NumSubordinates; i++) begin : gen_sub
    // downstream
    axi4_slave #(
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
        .MAX_PENDING_RD(MaxPendingRd),
        .MAX_PENDING_WR(MaxPendingWr),
        .CONFIG_WDATA_MASKED(0),
        .CONFIG_RDATA_MASKED(0),
        .READ_INTERLEAVE_ON(0),
        .ALLOW_SPARSE_STROBE(1),
        .BYTE_STROBE_ON(1)
    ) downstream (
        // Global signals
        .aclk    (clk),
        .aresetn (!rst),
        .csysreq ('d1),
        .csysack ('d1),
        .cactive ('d1),
        // Write Address Channel
        .awvalid (downstream_awvalid[i]),
        .awready (downstream_awready[i]),
        .awid    (downstream_awid[i]),
        .awaddr  (downstream_awaddr[i]),
        .awlen   (downstream_awlen[i]),
        .awsize  (downstream_awsize[i]),
        .awburst (downstream_awburst[i]),
        .awuser  (downstream_awuser[i]),
        .awprot  (downstream_awprot[i]),
        .awlock  ('d0),
        .awcache (downstream_awcache[i]),
        .awqos   ('d0),
        .awregion('d0),
        // Write Channel
        .wvalid  (downstream_wvalid[i]),
        .wready  (downstream_wready[i]),
        .wdata   (downstream_wdata[i]),
        .wstrb   (downstream_wstrb[i]),
        .wlast   (downstream_wlast[i]),
        .wuser   (downstream_wuser[i]),
        // Write Response channel
        .bvalid  (downstream_bvalid[i]),
        .bready  (downstream_bready[i]),
        .bid     (downstream_bid[i]),
        .bresp   (downstream_bresp[i]),
        .buser   (downstream_buser[i]),
        // Read Address Channel
        .arvalid (downstream_arvalid[i]),
        .arready (downstream_arready[i]),
        .arid    (downstream_arid[i]),
        .araddr  (downstream_araddr[i]),
        .arlen   (downstream_arlen[i]),
        .arsize  (downstream_arsize[i]),
        .arburst (downstream_arburst[i]),
        .aruser  (downstream_aruser[i]),
        .arprot  (downstream_arprot[i]),
        .arlock  ('d0),
        .arcache (downstream_arcache[i]),
        .arqos   ('d0),
        .arregion('d0),
        // Read Channel
        .rvalid  (downstream_rvalid[i]),
        .rready  (downstream_rready[i]),
        .ruser   (downstream_ruser[i]),
        .rid     (downstream_rid[i]),
        .rdata   (downstream_rdata[i]),
        .rresp   (downstream_rresp[i]),
        .rlast   (downstream_rlast[i])
    );
  end

endmodule : br_amba_axi_demux_fpv_monitor

bind br_amba_axi_demux br_amba_axi_demux_fpv_monitor #(
    .NumSubordinates(NumSubordinates),
    .AwAxiIdWidth(AwAxiIdWidth),
    .ArAxiIdWidth(ArAxiIdWidth),
    .AwMaxOutstandingPerId(AwMaxOutstandingPerId),
    .ArMaxOutstandingPerId(ArMaxOutstandingPerId),
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
) monitor (.*);
