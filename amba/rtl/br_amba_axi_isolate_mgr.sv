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
//
// Bedrock-RTL AXI Upstream (Manager) Isolator
//
// This module is used to isolate an upstream AXI manager from a downstream
// AXI subordinate such that the upstream manager can be reset while
// maintaining the protocol integrity of the downstream interconnect.
//
// Isolation is requested by asserting the isolate_req signal and holding
// it for the duration of the isolation. Isolation is complete (and
// upstream manager may be safely reset) when the isolate_done signal
// asserts in response to the assertion of isolate_req.
//
// Once the upstream manager is ready to re-connect, the isolate_req
// signal may be deasserted and the manager will resume normal
// operation. The isolate_done signal will deassert in response to the
// deassertion of isolate_req, after which new transactions will be forwarded
// from upstream->downstream normally.
//
// Isolation is guaranteed to complete without any assumption about the
// state of the upstream interface and may be used to recover in cases
// where a manager becomes stuck or otherwise unable to make forward
// progress.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_amba_axi_isolate_mgr #(
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
    // Maximum allowed skew (measured in max-length transactions)
    // that can be tracked between AW and W channels without causing
    // backpressure on the upstream ports.
    parameter int MaxTransactionSkew = 2,
    // Maximum number of response beats per transaction. Can be set
    // to 1 for AXI-Lite, otherwise must be set to
    // br_amba::AxiBurstLenWidth.
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    // WUSER data to generate for isolated transactions.
    parameter bit [WUserWidth-1:0] IsolateWUser = '0,
    // WDATA data to generate for isolated transactions.
    parameter bit [DataWidth-1:0] IsolateWData = '0,
    // WSTRB data to generate for isolated transactions.
    parameter bit [(DataWidth/8)-1:0] IsolateWStrb = '0,
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

  `BR_ASSERT_STATIC(max_outstanding_gt_1_a, MaxOutstanding > 1)
  `BR_ASSERT_STATIC(burst_len_legal_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  // Check that the isolate request can only rise when isolate_done is false.
  `BR_ASSERT_INTG(legal_request_rise_a, $rose(isolate_req) |-> !isolate_done)
  // Check that the isolate request can only fall when isolate_done is true.
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> isolate_done)

  //
  // Internal Signals
  //

  logic downstream_awready_int;
  logic downstream_awvalid_int;
  logic [AddrWidth-1:0] downstream_awaddr_int;
  logic [IdWidth-1:0] downstream_awid_int;
  logic [br_amba::AxiBurstSizeWidth-1:0] downstream_awsize_int;
  logic [br_amba::AxiBurstTypeWidth-1:0] downstream_awburst_int;
  logic [br_amba::AxiProtWidth-1:0] downstream_awprot_int;
  logic [AWUserWidth-1:0] downstream_awuser_int;
  logic [AxiBurstLenWidth-1:0] downstream_awlen_int;

  logic downstream_wready_int;
  logic downstream_wvalid_int;
  logic [DataWidth-1:0] downstream_wdata_int;
  logic [StrobeWidth-1:0] downstream_wstrb_int;
  logic [WUserWidth-1:0] downstream_wuser_int;
  logic downstream_wlast_int;

  logic downstream_arready_int;
  logic downstream_arvalid_int;
  logic [AddrWidth-1:0] downstream_araddr_int;
  logic [IdWidth-1:0] downstream_arid_int;
  logic [br_amba::AxiBurstSizeWidth-1:0] downstream_arsize_int;
  logic [br_amba::AxiBurstTypeWidth-1:0] downstream_arburst_int;
  logic [br_amba::AxiProtWidth-1:0] downstream_arprot_int;
  logic [ARUserWidth-1:0] downstream_aruser_int;
  logic [AxiBurstLenWidth-1:0] downstream_arlen_int;

  //
  // Write Path
  //

  logic upstream_awready_iso;
  logic upstream_awvalid_iso;
  //
  logic isolate_done_w;
  logic align_and_hold_req_w;
  logic align_and_hold_done_w;
  logic req_tracker_isolate_req_w;
  logic req_tracker_isolate_done_w;

  br_amba_iso_us_fsm br_amba_iso_us_fsm_w (
      .clk,
      .rst,
      //
      .isolate_req,
      .isolate_done(isolate_done_w),
      //
      .align_and_hold_req(align_and_hold_req_w),
      .align_and_hold_done(align_and_hold_done_w),
      //
      .req_tracker_isolate_req(req_tracker_isolate_req_w),
      .req_tracker_isolate_done(req_tracker_isolate_done_w)
  );

  br_amba_iso_wdata_align #(
      .MaxTransactionSkew(MaxTransactionSkew),
      .MaxAxiBurstLen(MaxAxiBurstLen),
      .AxiBurstLenWidth(AxiBurstLenWidth),
      .PreventExcessData(1),
      .FakeWriteDataOnAlign(1)
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
      .upstream_wlast,
      //
      .downstream_awready (upstream_awready_iso),
      .downstream_awvalid (upstream_awvalid_iso),
      //
      .downstream_wready  (downstream_wready_int),
      .downstream_wvalid  (downstream_wvalid_int),
      .downstream_wlast   (downstream_wlast_int)
  );

  br_amba_iso_req_tracker #(
      .MaxOutstanding(MaxOutstanding)
  ) br_amba_iso_req_tracker_w (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_awready_iso),
      .upstream_axvalid(upstream_awvalid_iso),
      //
      .upstream_xready(upstream_bready),
      .upstream_xvalid(upstream_bvalid),
      .upstream_xlast(),
      //
      .downstream_axready(downstream_awready_int),
      .downstream_axvalid(downstream_awvalid_int),
      //
      .downstream_xready(downstream_bready),
      .downstream_xvalid(downstream_bvalid),
      .downstream_xlast(1'b1),
      //
      .isolate_req(req_tracker_isolate_req_w),
      .isolate_done(req_tracker_isolate_done_w)
  );

  // Need to insert fake data values on the downstream W channel during write alignment.
  logic use_fake_w_data;
  assign use_fake_w_data = align_and_hold_req_w;

  assign downstream_wuser_int = use_fake_w_data ? IsolateWUser : upstream_wuser;
  assign downstream_wdata_int = use_fake_w_data ? IsolateWData : upstream_wdata;
  assign downstream_wstrb_int = use_fake_w_data ? IsolateWStrb : upstream_wstrb;

  // Pass-through signals
  assign downstream_awaddr_int = upstream_awaddr;
  assign downstream_awid_int = upstream_awid;
  assign downstream_awsize_int = upstream_awsize;
  assign downstream_awburst_int = upstream_awburst;
  assign downstream_awlen_int = upstream_awlen;
  assign downstream_awprot_int = upstream_awprot;
  assign downstream_awuser_int = upstream_awuser;
  //
  assign upstream_bid = downstream_bid;
  assign upstream_buser = downstream_buser;
  assign upstream_bresp = downstream_bresp;

  //
  // Read Path
  //

  logic upstream_arready_iso;
  logic upstream_arvalid_iso;
  //
  logic isolate_done_r;
  logic align_and_hold_req_r;
  logic align_and_hold_done_r;
  logic req_tracker_isolate_req_r;
  logic req_tracker_isolate_done_r;

  br_amba_iso_us_fsm br_amba_iso_us_fsm_r (
      .clk,
      .rst,
      //
      .isolate_req,
      .isolate_done(isolate_done_r),
      //
      .align_and_hold_req(align_and_hold_req_r),
      .align_and_hold_done(align_and_hold_done_r),
      //
      .req_tracker_isolate_req(req_tracker_isolate_req_r),
      .req_tracker_isolate_done(req_tracker_isolate_done_r)
  );

  // No alignment needed (since there is only a single read request channel),
  // just simple backpressure of upstream read requests.
  logic upstream_blocked_r;

  assign upstream_blocked_r = align_and_hold_req_r || align_and_hold_done_r;
  assign align_and_hold_done_r = align_and_hold_req_r;
  assign upstream_arvalid_iso = upstream_arvalid && !upstream_blocked_r;
  assign upstream_arready = upstream_arready_iso && !upstream_blocked_r;

  br_amba_iso_req_tracker #(
      .MaxOutstanding(MaxOutstanding)
  ) br_amba_iso_req_tracker_r (
      .clk,
      .rst,
      //
      .upstream_axready(upstream_arready_iso),
      .upstream_axvalid(upstream_arvalid_iso),
      //
      .upstream_xready(upstream_rready),
      .upstream_xvalid(upstream_rvalid),
      .upstream_xlast(upstream_rlast),
      //
      .downstream_axready(downstream_arready_int),
      .downstream_axvalid(downstream_arvalid_int),
      //
      .downstream_xready(downstream_rready),
      .downstream_xvalid(downstream_rvalid),
      .downstream_xlast(downstream_rlast),
      //
      .isolate_req(req_tracker_isolate_req_r),
      .isolate_done(req_tracker_isolate_done_r)
  );

  // Pass-through signals
  assign downstream_araddr_int = upstream_araddr;
  assign downstream_arid_int = upstream_arid;
  assign downstream_arsize_int = upstream_arsize;
  assign downstream_arburst_int = upstream_arburst;
  assign downstream_arlen_int = upstream_arlen;
  assign downstream_arprot_int = upstream_arprot;
  assign downstream_aruser_int = upstream_aruser;
  //
  assign upstream_rdata = downstream_rdata;
  assign upstream_rresp = downstream_rresp;
  assign upstream_ruser = downstream_ruser;
  assign upstream_rid = downstream_rid;

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

  // Assertions
  `BR_ASSERT(no_accept_ar_when_isolated_a, isolate_done_r |-> !upstream_arready)
  `BR_ASSERT(no_accept_aw_when_isolated_a, isolate_done_w |-> !upstream_awready)
  `BR_ASSERT(no_accept_w_when_isolated_a, isolate_done_w |-> !upstream_wready)

  //
  // Downstream Output Register Stage
  //

  // This flop stage is needed to ensure that valid stability (required by AMBA protocol)
  // is maintained on the downstream ports when entering isolation.

  br_flow_reg_fwd #(
      .Width($bits(
          downstream_awaddr_int
      ) + $bits(
          downstream_awid_int
      ) + $bits(
          downstream_awsize_int
      ) + $bits(
          downstream_awburst_int
      ) + $bits(
          downstream_awlen_int
      ) + $bits(
          downstream_awprot_int
      ) + $bits(
          downstream_awuser_int
      )),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_ds_aw (
      .clk,
      .rst,
      //
      .push_valid(downstream_awvalid_int),
      .push_data({
        downstream_awaddr_int,
        downstream_awid_int,
        downstream_awsize_int,
        downstream_awburst_int,
        downstream_awlen_int,
        downstream_awprot_int,
        downstream_awuser_int
      }),
      .push_ready(downstream_awready_int),
      //
      .pop_valid(downstream_awvalid),
      .pop_data({
        downstream_awaddr,
        downstream_awid,
        downstream_awsize,
        downstream_awburst,
        downstream_awlen,
        downstream_awprot,
        downstream_awuser
      }),
      .pop_ready(downstream_awready)
  );

  br_flow_reg_fwd #(
      .Width($bits(
          downstream_wdata_int
      ) + $bits(
          downstream_wstrb_int
      ) + $bits(
          downstream_wuser_int
      ) + $bits(
          downstream_wlast_int
      )),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_ds_w (
      .clk,
      .rst,
      //
      .push_valid(downstream_wvalid_int),
      .push_data({
        downstream_wdata_int, downstream_wstrb_int, downstream_wuser_int, downstream_wlast_int
      }),
      .push_ready(downstream_wready_int),
      //
      .pop_valid(downstream_wvalid),
      .pop_data({downstream_wdata, downstream_wstrb, downstream_wuser, downstream_wlast}),
      .pop_ready(downstream_wready)
  );

  br_flow_reg_fwd #(
      .Width($bits(
          downstream_araddr_int
      ) + $bits(
          downstream_arid_int
      ) + $bits(
          downstream_arsize_int
      ) + $bits(
          downstream_arburst_int
      ) + $bits(
          downstream_arlen_int
      ) + $bits(
          downstream_arprot_int
      ) + $bits(
          downstream_aruser_int
      )),
      .EnableAssertPushValidStability(0),
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_fwd_ds_ar (
      .clk,
      .rst,
      //
      .push_valid(downstream_arvalid_int),
      .push_data({
        downstream_araddr_int,
        downstream_arid_int,
        downstream_arsize_int,
        downstream_arburst_int,
        downstream_arlen_int,
        downstream_arprot_int,
        downstream_aruser_int
      }),
      .push_ready(downstream_arready_int),
      //
      .pop_valid(downstream_arvalid),
      .pop_data({
        downstream_araddr,
        downstream_arid,
        downstream_arsize,
        downstream_arburst,
        downstream_arlen,
        downstream_arprot,
        downstream_aruser
      }),
      .pop_ready(downstream_arready)
  );

endmodule
