module br_amba_axi_iso_ds #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 1,
    parameter int AWUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int BUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter int MaxOutstanding = 128,
    parameter int AxiIdCount = 2 ** IdWidth,
    parameter int MaxTransactionSkew = 2,
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    parameter br_amba::AxiRespWidth IsolateResp = br_amba::AxiRespSlverr,
    parameter bit [BUserWidth-1:0] IsolateBUser = '0,
    parameter bit [RUserWidth-1:0] IsolateRUser = '0,
    parameter bit [DataWidth-1:0] IsolateRData = '0,
    parameter bit FlopPtrRamRd = 1,
    parameter bit FlopDataRamRd = 1,
    localparam int StrobeWidth = DataWidth / 8
) (
    input  logic                                  clk,
    input  logic                                  rst,
    //
    input  logic                                  isolate_req,
    output logic                                  isolate_done,
    //
    input  logic [                 AddrWidth-1:0] upstream_awaddr,
    input  logic [                   IdWidth-1:0] upstream_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] upstream_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] upstream_awprot,
    input  logic [               AWUserWidth-1:0] upstream_awuser,
    input  logic                                  upstream_awvalid,
    output logic                                  upstream_awready,
    input  logic [                 DataWidth-1:0] upstream_wdata,
    input  logic [               StrobeWidth-1:0] upstream_wstrb,
    input  logic [                WUserWidth-1:0] upstream_wuser,
    input  logic                                  upstream_wlast,
    input  logic                                  upstream_wvalid,
    output logic                                  upstream_wready,
    output logic [                   IdWidth-1:0] upstream_bid,
    output logic [                BUserWidth-1:0] upstream_buser,
    output logic [     br_amba::AxiRespWidth-1:0] upstream_bresp,
    output logic                                  upstream_bvalid,
    input  logic                                  upstream_bready,
    input  logic [                 AddrWidth-1:0] upstream_araddr,
    input  logic [                   IdWidth-1:0] upstream_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] upstream_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] upstream_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] upstream_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] upstream_arprot,
    input  logic [               ARUserWidth-1:0] upstream_aruser,
    input  logic                                  upstream_arvalid,
    output logic                                  upstream_arready,
    output logic [                   IdWidth-1:0] upstream_rid,
    output logic [                 DataWidth-1:0] upstream_rdata,
    output logic [                RUserWidth-1:0] upstream_ruser,
    output logic [     br_amba::AxiRespWidth-1:0] upstream_rresp,
    output logic                                  upstream_rlast,
    output logic                                  upstream_rvalid,
    input  logic                                  upstream_rready,
    //
    output logic [                 AddrWidth-1:0] downstream_awaddr,
    output logic [                   IdWidth-1:0] downstream_awid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] downstream_awlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] downstream_awsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] downstream_awburst,
    output logic [     br_amba::AxiProtWidth-1:0] downstream_awprot,
    output logic [               AWUserWidth-1:0] downstream_awuser,
    output logic                                  downstream_awvalid,
    input  logic                                  downstream_awready,
    output logic [                 DataWidth-1:0] downstream_wdata,
    output logic [               StrobeWidth-1:0] downstream_wstrb,
    output logic [                WUserWidth-1:0] downstream_wuser,
    output logic                                  downstream_wlast,
    output logic                                  downstream_wvalid,
    input  logic                                  downstream_wready,
    input  logic [                   IdWidth-1:0] downstream_bid,
    input  logic [                BUserWidth-1:0] downstream_buser,
    input  logic [     br_amba::AxiRespWidth-1:0] downstream_bresp,
    input  logic                                  downstream_bvalid,
    output logic                                  downstream_bready,
    output logic [                 AddrWidth-1:0] downstream_araddr,
    output logic [                   IdWidth-1:0] downstream_arid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] downstream_arlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] downstream_arsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] downstream_arburst,
    output logic [     br_amba::AxiProtWidth-1:0] downstream_arprot,
    output logic [               ARUserWidth-1:0] downstream_aruser,
    output logic                                  downstream_arvalid,
    input  logic                                  downstream_arready,
    input  logic [                   IdWidth-1:0] downstream_rid,
    input  logic [                 DataWidth-1:0] downstream_rdata,
    input  logic [                RUserWidth-1:0] downstream_ruser,
    input  logic [     br_amba::AxiRespWidth-1:0] downstream_rresp,
    input  logic                                  downstream_rlast,
    input  logic                                  downstream_rvalid,
    output logic                                  downstream_rready
);

  //
  // Write Path
  //

  logic downstream_wready_iso;
  logic downstream_wvalid_iso;
  logic downstream_awready_iso;
  logic downstream_awvalid_iso;
  logic upstream_awready_holdoff;
  logic upstream_awvalid_holdoff;
  logic upstream_awready_tracker;
  logic upstream_awvalid_tracker;
  //
  logic isolate_done_w;
  logic align_and_hold_req_w;
  logic align_and_hold_done_w;
  logic isolate_req_w;
  logic resp_tracker_fifo_empty_w;

  br_amba_iso_ds_fsm br_amba_iso_ds_fsm_w (
      .clk,
      .rst,
      //
      .isolate_req,
      .isolate_done(isolate_done_w),
      //
      .align_and_hold_req(align_and_hold_req_w),
      .align_and_hold_done(align_and_hold_done_w),
      //
      .isolate_req(isolate_req_w),
      //
      .resp_tracker_fifo_empty(resp_tracker_fifo_empty_w)
  );

  br_amba_iso_wdata_align #(
      .MaxTransactionSkew(MaxTransactionSkew),
      .MaxAxiBurstLen(MaxAxiBurstLen)
  ) br_amba_iso_wdata_align_w (
      .clk,
      .rst,
      //
      .align_and_hold_req (align_and_hold_req_w),
      .align_and_hold_done(align_and_hold_done_w),
      //
      .upstream_awready,
      .upstream_awvalid,
      .upstream_awlen,
      //
      .upstream_wready,
      .upstream_wvalid,
      //
      .downstream_awready (upstream_awready_holdoff),
      .downstream_awvalid (upstream_awvalid_holdoff),
      //
      .downstream_wready  (downstream_wready_iso),
      .downstream_wvalid  (downstream_wvalid_iso),
  );

  br_flow_fork #(
      .NumFlows(2)
  ) br_flow_fork_aw (
      .clk,
      .rst,
      //
      .push_ready(upstream_awready_holdoff),
      .push_valid(upstream_awvalid_holdoff),
      //
      .pop_ready({downstream_awready_iso, upstream_awready_tracker}),
      .pop_valid_unstable({downstream_awvalid_iso, upstream_awvalid_tracker})
  );

  br_amba_iso_resp_tracker #(
      .MaxOutstanding(MaxOutstanding),
      .AxiIdCount(AxiIdCount),
      .AxiIdWidth(IdWidth),
      .DataWidth(BUserWidth),
      .FlopPtrRamRd(FlopPtrRamRd),
      .FlopDataRamRd(FlopDataRamRd),
      .IsolateResp(IsolateResp),
      .IsolateData(IsolateBUser),
      // Single write response beat per write transaction
      .MaxAxiBurstLen(1),
  ) br_amba_iso_resp_tracker_w (
      .clk,
      .rst,
      //
      .isolate_req(isolate_req_w),
      .resp_fifo_empty(resp_tracker_fifo_empty_w),
      //
      .upstream_axready(upstream_awready_tracker),
      .upstream_axvalid(upstream_awvalid_tracker),
      .upstream_axid(upstream_awid),
      .upstream_axlen(upstream_awlen),
      //
      .upstream_xready(upstream_bready),
      .upstream_xvalid(upstream_bvalid),
      .upstream_xid(upstream_bid),
      .upstream_xresp(upstream_bresp),
      .upstream_xlast(upstream_bvalid),
      .upstream_xdata(upstream_buser),
      //
      .downstream_xready(downstream_bready),
      .downstream_xvalid(downstream_bvalid),
      .downstream_xid(downstream_bid),
      .downstream_xresp(downstream_bresp),
      .downstream_xlast(downstream_bvalid),
      .downstream_xdata(downstream_buser)
  );

  // When isolating, downstream AW/W valid are forced to 1'b0, downstream
  // ready are forced to 1'b1 (incoming requests are discarded instead of
  // being passed downstream)
  assign downstream_wvalid = downstream_wvalid_iso && !isolate_req_w;
  assign downstream_wready_iso = downstream_wready || isolate_req_w;
  assign downstream_awvalid = downstream_awvalid_iso && !isolate_req_w;
  assign downstream_awready_iso = downstream_awready || isolate_req_w;

  // Pass-through signals
  assign downstream_awaddr = upstream_awaddr;
  assign downstream_awid = upstream_awid;
  assign downstream_awlen = upstream_awlen;
  assign downstream_awsize = upstream_awsize;
  assign downstream_awburst = upstream_awburst;
  assign downstream_awprot = upstream_awprot;
  assign downstream_awuser = upstream_awuser;
  //
  assign downstream_wdata = upstream_wdata;
  assign downstream_wstrb = upstream_wstrb;
  assign downstream_wuser = upstream_wuser;
  assign downstream_wlast = upstream_wlast;

  //
  // Read Path
  //
  logic downstream_arready_iso;
  logic downstream_arvalid_iso;
  logic upstream_arready_holdoff;
  logic upstream_arvalid_holdoff;
  logic upstream_arready_tracker;
  logic upstream_arvalid_tracker;
  //
  logic isolate_done_r;
  logic align_and_hold_req_r;
  logic align_and_hold_done_r;
  logic isolate_req_r;
  logic resp_tracker_fifo_empty_r;

  br_amba_iso_ds_fsm br_amba_iso_ds_fsm_r (
      .clk,
      .rst,
      //
      .isolate_req,
      .isolate_done(isolate_done_r),
      //
      .align_and_hold_req(align_and_hold_req_r),
      .align_and_hold_done(align_and_hold_done_r),
      //
      .isolate_req(isolate_req_r),
      //
      .resp_tracker_fifo_empty(resp_tracker_fifo_empty_r)
  );

  // No alignment needed (since there is only a single read request channel),
  // just simple backpressure.
  assign upstream_arvalid_holdoff = upstream_arvalid && !align_and_hold_req_r;
  assign upstream_arready = upstream_arready_holdoff && !align_and_hold_req_r;
  assign align_and_hold_done_r = align_and_hold_req_r;

  br_flow_fork #(
      .NumFlows(2)
  ) br_flow_fork_ar (
      .clk,
      .rst,
      //
      .push_ready(upstream_arready_holdoff),
      .push_valid(upstream_arvalid_holdoff),
      //
      .pop_ready({downstream_arready_iso, upstream_arready_tracker}),
      .pop_valid_unstable({downstream_arvalid_iso, upstream_arvalid_tracker})
  );

  br_amba_iso_resp_tracker #(
      .MaxOutstanding(MaxOutstanding),
      .AxiIdCount(AxiIdCount),
      .AxiIdWidth(IdWidth),
      .DataWidth(RUserWidth + DataWidth),
      .FlopPtrRamRd(FlopPtrRamRd),
      .FlopDataRamRd(FlopDataRamRd),
      .IsolateResp(IsolateResp),
      .IsolateData({IsolateRUser, IsolateRData}),
      // MaxAxiBurstLen response beats per read transaction
      .MaxAxiBurstLen(MaxAxiBurstLen),
  ) br_amba_iso_resp_tracker_r (
      .clk,
      .rst,
      //
      .isolate_req(isolate_req_r),
      .resp_fifo_empty(resp_tracker_fifo_empty_r),
      //
      .upstream_axready(upstream_arready_tracker),
      .upstream_axvalid(upstream_arvalid_tracker),
      .upstream_axid(upstream_arid),
      .upstream_axlen(upstream_arlen),
      //
      .upstream_xready(upstream_rready),
      .upstream_xvalid(upstream_rvalid),
      .upstream_xid(upstream_rid),
      .upstream_xresp(upstream_rresp),
      .upstream_xlast(upstream_rlast),
      .upstream_xdata({upstream_ruser, upstream_rdata}),
      //
      .downstream_xready(downstream_rready),
      .downstream_xvalid(downstream_rvalid),
      .downstream_xid(downstream_rid),
      .downstream_xresp(downstream_rresp),
      .downstream_xlast(downstream_rlast),
      .downstream_xdata({downstream_ruser, downstream_rdata})
  );

  // When isolating, downstream AR valid are forced to 1'b0, downstream
  // ready are forced to 1'b1 (incoming requests are discarded instead of
  // being passed downstream)
  assign downstream_arvalid = downstream_arvalid_iso && !isolate_req_r;
  assign downstream_arready_iso = downstream_arready || isolate_req_r;

  // Pass-through signals
  assign downstream_araddr = upstream_araddr;
  assign downstream_arid = upstream_arid;
  assign downstream_arlen = upstream_arlen;
  assign downstream_arsize = upstream_arsize;
  assign downstream_arburst = upstream_arburst;
  assign downstream_arprot = upstream_arprot;
  assign downstream_aruser = upstream_aruser;

  //
  // Done Output
  //

  logic isolate_done_next;
  assign isolate_done_next = isolate_req ?
                            (isolate_done_w && isolate_done_r)
                            : !(isolate_done_w || isolate_done_r);

  `BR_REG(isolate_done, isolate_done_next)

endmodule
