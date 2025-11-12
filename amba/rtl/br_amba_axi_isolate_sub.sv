// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL AXI Downstream (Subordinate) Isolator
//
// This module is used to isolate a downstream AXI subordinate from an
// upstream AXI manager such that the downstream subordinate can be reset
// while maintaining the protocol integrity of the upstream interconnect.
//
// The isolator will generate responses for any transactions that are
// pending on the downstream side when isolation is requested and continue
// generating responses for any new transactions destined for the
// subordinate while the subordinate is isolated.
//
// Isolation is requested by asserting the isolate_req signal and holding
// it for the duration of the isolation. Isolation is complete (and
// downstream subordinate may be safely reset) when the isolate_done
// signal asserts in response to the assertion of isolate_req.
//
// Once the downstream subordinate is ready to re-connect, the isolate_req
// signal may be deasserted and the subordinate will resume normal
// operation. The isolate_done signal will deassert in response to the
// deassertion of isolate_req. Any new transactions accepted after
// isolate_done deasserts (as long as isolate_req remains low) are
// guaranteed to pass to the downstream.
//
// Read response data interleaving is not supported.
//
// Isolation is guaranteed to complete without any assumption about the
// state of the downstream interface and may be used to recover in cases
// where a subordinate becomes stuck or otherwise unable to make forward
// progress.

`include "br_registers.svh"
`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_amba_axi_isolate_sub #(
    // Width of the AXI address field.
    parameter int AddrWidth = 12,
    // Width of the AXI data field.
    parameter int DataWidth = 32,
    // Width of the AXI ID field.
    parameter int IdWidth = 1,
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
    // Maximum number of outstanding requests that can be tracked
    // without backpressuring the upstream request ports. Must be at least 2.
    parameter int MaxOutstanding = 128,
    // Number of unique AXI IDs that can be tracked. Must be less
    // than or equal to 2^IdWidth. Valid ids are 0 to AxiIdCount-1.
    parameter int AxiIdCount = 2 ** IdWidth,
    // Maximum allowed skew (measured in max-length transactions)
    // that can be tracked between AW and W channels without causing
    // backpressure on the upstream ports.
    parameter int MaxTransactionSkew = 2,
    // Maximum number of response beats per transaction. Can be set
    // to 1 for AXI-Lite, otherwise must be set to
    // br_amba::AxiBurstLenWidth.
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    // Response to generate for isolated transactions.
    parameter br_amba::axi_resp_t IsolateResp = br_amba::AxiRespSlverr,
    // BUSER data to generate for isolated transactions.
    parameter bit [BUserWidth-1:0] IsolateBUser = '0,
    // RUSER data to generate for isolated transactions.
    parameter bit [RUserWidth-1:0] IsolateRUser = '0,
    // RDATA data to generate for isolated transactions.
    parameter bit [DataWidth-1:0] IsolateRData = '0,
    // Set to 1 to use a dynamic storage shared FIFO for the read tracking
    // list.
    parameter bit UseDynamicFifoForReadTracker = 1,
    // When UseDynamicFifoForReadTracker=0, this parameter controls the depth
    // of the Per-ID tracking FIFO. This defaults to MaxOutstanding, but may
    // need to be set to a smaller value as the storage will be replicated for
    // each ID.
    parameter int StaticPerIdReadTrackerFifoDepth = MaxOutstanding,
    // Number of pipeline stages to use for the pointer RAM read data in the
    // response tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoPointerRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the data RAM read data in the
    // response tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoDataRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the pointer RAM address in the
    // response tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoPointerRamAddressDepthStages = 1,
    // Number of pipeline stages to use for the data RAM address in the
    // response tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoDataRamAddressDepthStages = 1,
    // Number of linked lists per FIFO in the response tracker FIFO. Has no
    // effect if AxiIdCount == 1 or UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoNumLinkedListsPerFifo = 2,
    // Number of pipeline stages to use for the staging buffer in the response
    // tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoStagingBufferDepth = 2,
    // Number of pipeline stages to use for the pop outputs in the response
    // tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoRegisterPopOutputs = 1,
    // Number of pipeline stages to use for the deallocation in the response
    // tracker FIFO. Has no effect if AxiIdCount == 1 or
    // UseDynamicFifoForReadTracker == 0.
    parameter int DynamicFifoRegisterDeallocation = 1,
    //
    localparam int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen),
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
    input  logic [          AxiBurstLenWidth-1:0] upstream_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] upstream_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] upstream_awburst,
    input  logic [    br_amba::AxiCacheWidth-1:0] upstream_awcache,
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
    input  logic [          AxiBurstLenWidth-1:0] upstream_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] upstream_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] upstream_arburst,
    input  logic [    br_amba::AxiCacheWidth-1:0] upstream_arcache,
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
    output logic [          AxiBurstLenWidth-1:0] downstream_awlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] downstream_awsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] downstream_awburst,
    output logic [    br_amba::AxiCacheWidth-1:0] downstream_awcache,
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
    output logic [          AxiBurstLenWidth-1:0] downstream_arlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] downstream_arsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] downstream_arburst,
    output logic [    br_amba::AxiCacheWidth-1:0] downstream_arcache,
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
  // Integration Checks
  //

  localparam int MinIdWidth = br_math::clamped_clog2(AxiIdCount);

  `BR_ASSERT_STATIC(max_outstanding_gt_1_a, MaxOutstanding > 1)
  `BR_ASSERT_STATIC(have_enough_ids_a, AxiIdCount <= 2 ** IdWidth)
  `BR_ASSERT_STATIC(burst_len_legal_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  // Check that the isolate request can only rise when isolate_done is false.
  `BR_ASSERT_INTG(legal_request_rise_a, $rose(isolate_req) |-> !isolate_done)
  // Check that the isolate request can only fall when isolate_done is true.
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> isolate_done)
  if (MinIdWidth < IdWidth) begin : gen_id_width_lt_len_width
    `BR_ASSERT_INTG(unused_upper_awid_zero_a,
                    upstream_awvalid |-> upstream_awid[IdWidth-1:MinIdWidth] == '0)
    `BR_ASSERT_INTG(unused_upper_arid_zero_a,
                    upstream_arvalid |-> upstream_arid[IdWidth-1:MinIdWidth] == '0)
  end

  //
  // Internal Signals
  //

  logic upstream_bready_int;
  logic upstream_bvalid_int;
  logic [br_amba::AxiRespWidth-1:0] upstream_bresp_int;
  logic [BUserWidth-1:0] upstream_buser_int;
  logic [IdWidth-1:0] upstream_bid_int;
  //
  logic upstream_rready_int;
  logic upstream_rvalid_int;
  logic upstream_rlast_int;
  logic [br_amba::AxiRespWidth-1:0] upstream_rresp_int;
  logic [RUserWidth-1:0] upstream_ruser_int;
  logic [IdWidth-1:0] upstream_rid_int;
  logic [DataWidth-1:0] upstream_rdata_int;

  //
  // Write Path
  //

  logic downstream_wready_iso;
  logic downstream_wvalid_iso;
  logic downstream_awready_iso;
  logic downstream_awvalid_iso;
  logic upstream_awready_holdoff;
  logic upstream_awvalid_holdoff;
  logic upstream_wready_holdoff;
  logic upstream_wvalid_holdoff;
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
      .resp_tracker_isolate_req(isolate_req_w),
      .resp_tracker_fifo_empty(resp_tracker_fifo_empty_w)
  );

  br_amba_iso_wdata_align #(
      .MaxTransactionSkew(MaxTransactionSkew),
      .MaxAxiBurstLen(MaxAxiBurstLen),
      .AxiBurstLenWidth(AxiBurstLenWidth)
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
      .upstream_wlast(1'b0),
      //
      .downstream_awready (upstream_awready_holdoff),
      .downstream_awvalid (upstream_awvalid_holdoff),
      //
      .downstream_wready  (upstream_wready_holdoff),
      .downstream_wvalid  (upstream_wvalid_holdoff),
      .downstream_wlast   ()
  );

  br_amba_iso_resp_tracker #(
      .MaxOutstanding(MaxOutstanding),
      .AxiIdCount(AxiIdCount),
      .AxiIdWidth(IdWidth),
      .DataWidth(BUserWidth),
      .DynamicFifoPointerRamReadDataDepthStages(DynamicFifoPointerRamReadDataDepthStages),
      .DynamicFifoPointerRamAddressDepthStages(DynamicFifoPointerRamAddressDepthStages),
      .DynamicFifoNumLinkedListsPerFifo(DynamicFifoNumLinkedListsPerFifo),
      .DynamicFifoDataRamReadDataDepthStages(DynamicFifoDataRamReadDataDepthStages),
      .DynamicFifoDataRamAddressDepthStages(DynamicFifoDataRamAddressDepthStages),
      .DynamicFifoStagingBufferDepth(DynamicFifoStagingBufferDepth),
      .DynamicFifoRegisterPopOutputs(DynamicFifoRegisterPopOutputs),
      .DynamicFifoRegisterDeallocation(DynamicFifoRegisterDeallocation),
      .IsolateResp(IsolateResp),
      .IsolateData(IsolateBUser),
      // Single write response beat per write transaction
      .MaxAxiBurstLen(1),
      .MaxTransactionSkew(MaxTransactionSkew),
      .EnableWlastTracking(1),
      // When MaxAxiBurstLen=1, the static FIFO implementation becomes an
      // array of counters (no actual FIFOs), which is always more efficient
      // than a dynamic FIFO. So no external option is provided to select a
      // dynamic FIFO.
      .UseDynamicFifo(0),
      .PerIdFifoDepth(MaxOutstanding)
  ) br_amba_iso_resp_tracker_w (
      .clk,
      .rst,
      //
      .isolate_req(isolate_req_w),
      .resp_fifo_empty(resp_tracker_fifo_empty_w),
      //
      .upstream_axready(upstream_awready_holdoff),
      .upstream_axvalid(upstream_awvalid_holdoff),
      .upstream_axid(upstream_awid),
      // write responses only have a single beat
      .upstream_axlen(1'b0),
      //
      .upstream_xready(upstream_bready_int),
      .upstream_xvalid(upstream_bvalid_int),
      .upstream_xid(upstream_bid_int),
      .upstream_xresp({upstream_bresp_int}),  // ri lint_check_waive ENUM_RHS
      .upstream_xlast(),
      .upstream_xdata(upstream_buser_int),
      //
      .upstream_wready(upstream_wready_holdoff),
      .upstream_wvalid(upstream_wvalid_holdoff),
      .upstream_wlast(upstream_wlast),
      //
      .downstream_axready(downstream_awready_iso),
      .downstream_axvalid(downstream_awvalid_iso),
      .downstream_axid(downstream_awid),
      .downstream_axlen(),
      //
      .downstream_wready(downstream_wready_iso),
      .downstream_wvalid(downstream_wvalid_iso),
      .downstream_wlast(downstream_wlast),
      //
      .downstream_xready(downstream_bready),
      .downstream_xvalid(downstream_bvalid),
      .downstream_xid(downstream_bid),
      .downstream_xresp(br_amba::axi_resp_t'(downstream_bresp)),
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
  assign downstream_awsize = upstream_awsize;
  assign downstream_awburst = upstream_awburst;
  assign downstream_awlen = upstream_awlen;
  assign downstream_awcache = upstream_awcache;
  assign downstream_awprot = upstream_awprot;
  assign downstream_awuser = upstream_awuser;
  //
  assign downstream_wdata = upstream_wdata;
  assign downstream_wstrb = upstream_wstrb;
  assign downstream_wuser = upstream_wuser;

  //
  // Read Path
  //
  logic downstream_arready_iso;
  logic downstream_arvalid_iso;
  logic upstream_arready_holdoff;
  logic upstream_arvalid_holdoff;
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
      .resp_tracker_isolate_req(isolate_req_r),
      .resp_tracker_fifo_empty(resp_tracker_fifo_empty_r)
  );

  // No alignment needed (since there is only a single read request channel),
  // just simple backpressure.
  assign upstream_arvalid_holdoff = upstream_arvalid && !align_and_hold_req_r;
  assign upstream_arready = upstream_arready_holdoff && !align_and_hold_req_r;
  assign align_and_hold_done_r = align_and_hold_req_r;

  br_amba_iso_resp_tracker #(
      .MaxOutstanding(MaxOutstanding),
      .AxiIdCount(AxiIdCount),
      .AxiIdWidth(IdWidth),
      .DataWidth(RUserWidth + DataWidth),
      .DynamicFifoPointerRamReadDataDepthStages(DynamicFifoPointerRamReadDataDepthStages),
      .DynamicFifoPointerRamAddressDepthStages(DynamicFifoPointerRamAddressDepthStages),
      .DynamicFifoNumLinkedListsPerFifo(DynamicFifoNumLinkedListsPerFifo),
      .DynamicFifoDataRamReadDataDepthStages(DynamicFifoDataRamReadDataDepthStages),
      .DynamicFifoDataRamAddressDepthStages(DynamicFifoDataRamAddressDepthStages),
      .DynamicFifoStagingBufferDepth(DynamicFifoStagingBufferDepth),
      .DynamicFifoRegisterPopOutputs(DynamicFifoRegisterPopOutputs),
      .DynamicFifoRegisterDeallocation(DynamicFifoRegisterDeallocation),
      .IsolateResp(IsolateResp),
      .IsolateData({IsolateRUser, IsolateRData}),
      // MaxAxiBurstLen response beats per read transaction
      .MaxAxiBurstLen(MaxAxiBurstLen),
      .EnableWlastTracking(0),
      .UseDynamicFifo(UseDynamicFifoForReadTracker),
      .PerIdFifoDepth(StaticPerIdReadTrackerFifoDepth)
  ) br_amba_iso_resp_tracker_r (
      .clk,
      .rst,
      //
      .isolate_req(isolate_req_r),
      .resp_fifo_empty(resp_tracker_fifo_empty_r),
      //
      .upstream_axready(upstream_arready_holdoff),
      .upstream_axvalid(upstream_arvalid_holdoff),
      .upstream_axid(upstream_arid),
      .upstream_axlen(upstream_arlen),
      //
      .upstream_wready(),
      .upstream_wvalid(1'b1),
      .upstream_wlast(1'b1),
      //
      .upstream_xready(upstream_rready_int),
      .upstream_xvalid(upstream_rvalid_int),
      .upstream_xid(upstream_rid_int),
      .upstream_xresp({upstream_rresp_int}),  // ri lint_check_waive ENUM_RHS
      .upstream_xlast(upstream_rlast_int),
      .upstream_xdata({upstream_ruser_int, upstream_rdata_int}),
      //
      .downstream_axready(downstream_arready_iso),
      .downstream_axvalid(downstream_arvalid_iso),
      .downstream_axid(downstream_arid),
      .downstream_axlen(downstream_arlen),
      //
      .downstream_wready(1'b1),
      .downstream_wvalid(),
      .downstream_wlast(),
      //
      .downstream_xready(downstream_rready),
      .downstream_xvalid(downstream_rvalid),
      .downstream_xid(downstream_rid),
      .downstream_xresp(br_amba::axi_resp_t'(downstream_rresp)),
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
  assign downstream_arsize = upstream_arsize;
  assign downstream_arburst = upstream_arburst;
  assign downstream_arcache = upstream_arcache;
  assign downstream_arprot = upstream_arprot;
  assign downstream_aruser = upstream_aruser;

  //
  // Done Output
  //

  logic isolate_done_next;

  // isolate_done is asserted when both write and read done signals rise
  // and deasserted after both done signals fall
  assign isolate_done_next = isolate_done ?
                            (isolate_done_w || isolate_done_r)
                            : (isolate_done_w && isolate_done_r);

  `BR_REG(isolate_done, isolate_done_next)

  //
  // Upstream Output Register Stage
  //

  // This flop stage is needed to ensure that valid stability (required by AMBA protocol)
  // is maintained on the upstream ports when entering isolation.

  br_flow_reg_fwd #(
      .Width($bits(
          upstream_rdata
      ) + $bits(
          upstream_rresp
      ) + $bits(
          upstream_rlast
      ) + $bits(
          upstream_ruser
      ) + $bits(
          upstream_rid
      )),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_us_r (
      .clk,
      .rst,
      //
      .push_ready(upstream_rready_int),
      .push_valid(upstream_rvalid_int),
      .push_data({
        upstream_rdata_int,
        upstream_rresp_int,
        upstream_rlast_int,
        upstream_ruser_int,
        upstream_rid_int
      }),
      //
      .pop_ready(upstream_rready),
      .pop_valid(upstream_rvalid),
      .pop_data({upstream_rdata, upstream_rresp, upstream_rlast, upstream_ruser, upstream_rid})
  );

  br_flow_reg_fwd #(
      .Width($bits(upstream_bresp) + $bits(upstream_buser) + $bits(upstream_bid)),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_us_aw (
      .clk,
      .rst,
      //
      .push_ready(upstream_bready_int),
      .push_valid(upstream_bvalid_int),
      .push_data ({upstream_bresp_int, upstream_buser_int, upstream_bid_int}),
      //
      .pop_ready (upstream_bready),
      .pop_valid (upstream_bvalid),
      .pop_data  ({upstream_bresp, upstream_buser, upstream_bid})
  );
endmodule
