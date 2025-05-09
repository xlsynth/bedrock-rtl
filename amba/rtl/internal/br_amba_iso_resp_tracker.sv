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
// Bedrock-RTL AXI Isolation Response Tracker and Generator
//
// This module monitors the AXI request channel from upstream to
// downstream and tracks the AxLEN values for every transaction
// currently pending on the downstream interface. An ordered list is
// maintained for each AXI ID and the tracked values are removed from
// the tracking list when a response is received on the downstream
// interface.
//
// When the isolate_req signal is asserted, the module will begin
// ignoring responses arriving on the downstream interface and instead
// generate error responses for all expected response beats for any
// transactions on the tracking lists. It will continue to accept new
// requests while isolate_req is asserted as well, and will
// continuously generate error responses on the pop side of the
// tracking list.
//
// The isolate_req signal may be safely deasserted when both of the
// following are true: 1. The resp_fifo_empty signal is asserted (all
// requests have been responded to) 2. The upstream_axvalid signal is
// deasserted (no new request is currently pending)
//
// Once the isolate_req signal is deasserted, the module will resume
// normal operation, forwarding requests to the downstream interface,
// and forwarding downstream responses to the upstream interface.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_iso_resp_tracker #(
    // Maximum allowed skew (measured in transactions) that can be tracked
    // without causing backpressure on the upstream ports.
    parameter int MaxTransactionSkew = 2,
    // Maximum number of outstanding requests that can be tracked without
    // backpressuring the upstream request ports.
    parameter int MaxOutstanding = 128,
    // Width of the AXI ID field.
    parameter int AxiIdWidth = 7,
    // Number of unique AXI IDs that can be tracked. Must be less than or
    // equal to 2^AxiIdWidth.
    parameter int AxiIdCount = 2 ** AxiIdWidth,
    // Width of the data field.
    parameter int DataWidth = 1,
    // Number of pipeline stages to use for the pointer RAM read data.
    parameter int FlopPtrRamRd = 0,
    // Number of pipeline stages to use for the data RAM read data.
    parameter int FlopDataRamRd = 0,
    // Response to generate for isolated transactions.
    parameter br_amba::axi_resp_t IsolateResp = br_amba::AxiRespSlverr,
    // Data to generate for isolated transactions.
    parameter bit [DataWidth-1:0] IsolateData = '0,
    // Can be set to 1 for AXI-Lite or write responses, otherwise should
    // be set to br_amba::AxiBurstLenWidth.
    parameter int MaxAxiBurstLen = 2 ** br_amba::AxiBurstLenWidth,
    // Enable tracking of WLAST for write responses. Set to 1 for write
    // tracking, 0 for read tracking.
    parameter bit EnableWlastTracking = 1,
    localparam int AxiBurstLenWidth = br_math::clamped_clog2(MaxAxiBurstLen)
) (
    input logic clk,
    input logic rst,
    // AW or AR channel from upstream
    output logic upstream_axready,
    input logic upstream_axvalid,
    input logic [AxiIdWidth-1:0] upstream_axid,
    input logic [AxiBurstLenWidth-1:0] upstream_axlen,
    // W channel from upstream
    output logic upstream_wready,
    input logic upstream_wvalid,
    input logic upstream_wlast,
    // R or B channel to upstream
    input logic upstream_xready,
    output logic upstream_xvalid,
    output logic [AxiIdWidth-1:0] upstream_xid,
    output br_amba::axi_resp_t upstream_xresp,
    output logic upstream_xlast,
    output logic [DataWidth-1:0] upstream_xdata,
    // AW or AR channel to downstream
    input logic downstream_axready,
    output logic downstream_axvalid,
    output logic [AxiIdWidth-1:0] downstream_axid,
    output logic [AxiBurstLenWidth-1:0] downstream_axlen,
    // W channel to downstream
    input logic downstream_wready,
    output logic downstream_wvalid,
    output logic downstream_wlast,
    // R or B channel from downstream
    output logic downstream_xready,
    input logic downstream_xvalid,
    input logic [AxiIdWidth-1:0] downstream_xid,
    input br_amba::axi_resp_t downstream_xresp,
    input logic [DataWidth-1:0] downstream_xdata,
    input logic downstream_xlast,
    //
    input logic isolate_req,
    output logic resp_fifo_empty
);

  // Integration checks
  `BR_ASSERT_STATIC(max_outstanding_gte_1_a, MaxOutstanding > 1)
  `BR_ASSERT_STATIC(max_outstanding_gt_skew_a, MaxOutstanding > MaxTransactionSkew)
  `BR_ASSERT_STATIC(max_axi_burst_len_1_or_amba_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  `BR_ASSERT_STATIC(axi_id_width_gte_clog2_a, AxiIdWidth >= $clog2(AxiIdCount))
  `BR_ASSERT_INTG(axlen_legal_range_a, upstream_axvalid |-> upstream_axlen < MaxAxiBurstLen)
  // Check that the isolate request can only fall when the tracker is empty and the upstream
  // is not driving a new request (because it is held off outside of this module).
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> $past(resp_fifo_empty) && !$past
                                        (upstream_axvalid))
  `BR_ASSERT_INTG(legal_axid_a, upstream_axvalid |-> upstream_axid < AxiIdCount)
  `BR_ASSERT_INTG(legal_xid_a, downstream_xvalid |-> downstream_xid < AxiIdCount)


  // Local parameters
  localparam bit SingleBeatOnly = (MaxAxiBurstLen == 1);
  localparam bit SingleIdOnly = (AxiIdCount == 1);
  localparam int MinIdWidth = br_math::clamped_clog2(AxiIdCount);
  localparam int OutstandingWidth = $clog2(MaxOutstanding + 1);

  // Local signals
  logic [AxiBurstLenWidth-1:0] tracker_fifo_push_len;
  logic [MinIdWidth-1:0] tracker_fifo_push_axid;
  logic tracker_fifo_push_valid;
  logic [AxiIdCount-1:0] tracker_fifo_pop_valid;
  logic [AxiIdCount-1:0] tracker_fifo_pop_ready;
  logic [AxiIdCount-1:0][AxiBurstLenWidth-1:0] tracker_fifo_pop_len;
  logic downstream_iso_xready;
  logic downstream_iso_xvalid;
  logic [AxiIdWidth-1:0] downstream_iso_xid;
  br_amba::axi_resp_t downstream_iso_xresp;
  logic [DataWidth-1:0] downstream_iso_xdata;
  logic reinit_count;
  logic incr_count;
  logic [AxiBurstLenWidth-1:0] resp_beat_count;
  logic x_beat;
  logic [AxiBurstLenWidth-1:0] cur_resp_len;
  logic cur_resp_valid;
  logic cur_resp_do_pop;
  logic [AxiIdWidth-1:0] cur_resp_id;
  logic [AxiIdWidth-1:0] iso_arb_id;
  logic iso_any_gnt;
  logic tracker_fifo_push_ready;
  logic final_count;
  logic zero_count;

  logic [AxiIdCount-1:0] tracker_fifo_pop_empty;
  logic staging_fifo_pop_empty;

  logic staging_fifo_push_valid;
  logic staging_fifo_push_ready;
  logic [AxiBurstLenWidth-1:0] staging_fifo_push_len;
  logic [MinIdWidth-1:0] staging_fifo_push_axid;

  logic can_accept_new_req;

  //
  // Write Data Receipt Tracking
  // Ensures a WLAST is received for every AWVALID received, prior to inserting into the tracking
  // FIFO. This is to ensure we can never generate (dummy, isolation) responses to writes where
  // we have not yet received the last beat of data from upstream on the W channel.
  //

  if (SingleBeatOnly) begin : gen_single_beat_only_len
    assign staging_fifo_push_len = 1'b0;
  end else begin : gen_multi_beat_len
    assign staging_fifo_push_len = upstream_axlen;
  end

  if (SingleIdOnly) begin : gen_single_id_only_axid
    assign staging_fifo_push_axid = '0;
  end else begin : gen_multi_id_only_axid
    assign staging_fifo_push_axid = upstream_axid[MinIdWidth-1:0];
  end

  assign staging_fifo_push_valid = upstream_axvalid && downstream_axready && can_accept_new_req;

  if (MinIdWidth < AxiIdWidth) begin : gen_id_width_lt_len_width
    `BR_UNUSED_NAMED(upstream_axid_unused, upstream_axid[AxiIdWidth-1:MinIdWidth])
    `BR_ASSERT_INTG(unused_upper_axid_zero_a,
                    upstream_axvalid |-> upstream_axid[AxiIdWidth-1:MinIdWidth] == '0)
  end

  // Total outstanding requests counters (in the staging+tracker FIFOs)
  logic [OutstandingWidth-1:0] total_req_count;
  br_counter #(
      .MaxValue(MaxOutstanding),
      .MaxChange(1),
      .EnableWrap(0),
      .EnableSaturate(0),
      .EnableReinitAndChange(0)
  ) br_counter_total_req (
      .clk,
      .rst,
      //
      .reinit(1'b0),
      .initial_value('0),
      .incr_valid(staging_fifo_push_valid && staging_fifo_push_ready),
      .incr(1'b1),
      .decr_valid(|(tracker_fifo_pop_valid & tracker_fifo_pop_ready)),
      .decr(1'b1),
      .value(total_req_count),
      .value_next()
  );

  // Need to ensure that the total outstanding requests held in the staging+tracker FIFOs
  // never exceeds the total amount of storage available in the tracker (multi-) FIFO. It
  // must be the case that everything in staging can eventually sink into the tracker FIFO
  // w/o requiring any pops from the tracker FIFO. Otherwise deadlock can result if a downstream
  // response arrives whose matching transaction is stuck in the staging FIFO (blocked by a
  // different ID).
  assign can_accept_new_req   = total_req_count < MaxOutstanding;

  if (EnableWlastTracking) begin : gen_wlast_tracking
    logic staging_fifo_pop_valid;
    logic staging_fifo_pop_ready;
    logic wlast_fifo_pop_valid;
    logic wlast_fifo_pop_ready;
    logic wlast_fifo_push_valid;
    logic wlast_fifo_push_valid_is_last;
    logic wlast_fifo_push_ready;
    logic can_accept_new_wlast;

    assign downstream_wlast = upstream_wlast;

    br_fifo_flops #(
        .Depth(MaxTransactionSkew),
        .Width(AxiBurstLenWidth + MinIdWidth),
        // valid can deassert if downstream_axready deasserts
        .EnableAssertPushValidStability(0)
    ) br_fifo_flops_aw_staging (
        .clk,
        .rst,
        //
        .push_valid(staging_fifo_push_valid),
        .push_data({staging_fifo_push_axid, staging_fifo_push_len}),
        .push_ready(staging_fifo_push_ready),
        //
        .pop_valid(staging_fifo_pop_valid),
        .pop_data({tracker_fifo_push_axid, tracker_fifo_push_len}),
        .pop_ready(staging_fifo_pop_ready),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        .empty(staging_fifo_pop_empty),
        .empty_next(),
        .items(),
        .items_next()
    );

    br_flow_fork #(
        .NumFlows(2),
        // If W beats are in excess when wdata alignment (during isolation) is requested, the
        // upstream valid can deassert without ready asserting.
        .EnableAssertPushValidStability(0)
    ) br_flow_fork_wlast_staging (
        .clk,
        .rst,
        //
        .push_valid(upstream_wvalid),
        .push_ready(upstream_wready),
        //
        .pop_valid_unstable({downstream_wvalid, wlast_fifo_push_valid}),
        .pop_ready({downstream_wready, (wlast_fifo_push_ready && can_accept_new_wlast)})
    );

    assign wlast_fifo_push_valid_is_last = wlast_fifo_push_valid
                                            && upstream_wlast
                                            && can_accept_new_wlast;

    br_fifo_flops #(
        .Depth(MaxTransactionSkew),
        .Width(1),
        // valid can deassert if downstream_wready deasserts
        .EnableAssertPushValidStability(0)
    ) br_fifo_flops_wlast_staging (
        .clk,
        .rst,
        //
        .push_valid(wlast_fifo_push_valid_is_last),
        .push_data(1'b0),
        .push_ready(wlast_fifo_push_ready),
        //
        .pop_valid(wlast_fifo_pop_valid),
        .pop_data(),
        .pop_ready(wlast_fifo_pop_ready),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );

    br_flow_join #(
        .NumFlows(2)
    ) br_flow_join_aw_staging (
        .clk,
        .rst,
        //
        .push_ready({staging_fifo_pop_ready, wlast_fifo_pop_ready}),
        .push_valid({staging_fifo_pop_valid, wlast_fifo_pop_valid}),
        //
        .pop_ready (tracker_fifo_push_ready),
        .pop_valid (tracker_fifo_push_valid)
    );

    // Total outstanding requests counters (in the staging+tracker FIFOs) for wlast staging
    logic [OutstandingWidth-1:0] total_wlast_count;
    br_counter #(
        .MaxValue(MaxOutstanding),
        .MaxChange(1),
        .EnableWrap(0),
        .EnableSaturate(0),
        .EnableReinitAndChange(0)
    ) br_counter_total_wlast (
        .clk,
        .rst,
        //
        .reinit(1'b0),
        .initial_value('0),
        .incr_valid(wlast_fifo_push_valid_is_last && wlast_fifo_push_ready),
        .incr(1'b1),
        .decr_valid(|(tracker_fifo_pop_valid & tracker_fifo_pop_ready)),
        .decr(1'b1),
        .value(total_wlast_count),
        .value_next()
    );

    assign can_accept_new_wlast = total_wlast_count < MaxOutstanding;

  end else begin : gen_no_wlast_tracking
    assign upstream_wready = 1'b0;
    `BR_UNUSED(upstream_wvalid)
    `BR_UNUSED(upstream_wlast)
    assign downstream_wlast  = 1'b0;
    assign downstream_wvalid = 1'b0;
    `BR_UNUSED(downstream_wready)

    assign tracker_fifo_push_valid = staging_fifo_push_valid;
    assign tracker_fifo_push_len = staging_fifo_push_len;
    assign tracker_fifo_push_axid = staging_fifo_push_axid;
    assign staging_fifo_push_ready = tracker_fifo_push_ready;
    assign staging_fifo_pop_empty = 1'b1;
  end

  //
  // Per-ID Request Tracker FIFO
  // Stores ordered list of request lengths for each ID.
  //

  if (SingleIdOnly) begin : gen_single_fifo
    br_fifo_flops #(
        .Depth(MaxOutstanding),
        .Width(AxiBurstLenWidth),
        .EnableBypass(1),
        .RegisterPopOutputs(1),
        // When EnableWlastTracking=0, valid can deassert if downstream_axready deasserts
        .EnableAssertPushValidStability(EnableWlastTracking)
    ) br_fifo_flops_req_tracker (
        .clk,
        .rst,
        //
        .push_valid(tracker_fifo_push_valid),
        .push_data(tracker_fifo_push_len),
        .push_ready(tracker_fifo_push_ready),
        //
        .pop_valid(tracker_fifo_pop_valid),
        .pop_data(tracker_fifo_pop_len),
        .pop_ready(tracker_fifo_pop_ready),
        //
        .full(),
        .full_next(),
        .slots(),
        .slots_next(),
        .empty(tracker_fifo_pop_empty),
        .empty_next(),
        .items(),
        .items_next()
    );
    `BR_UNUSED(tracker_fifo_push_axid)
  end else begin : gen_multi_fifo
    br_fifo_shared_dynamic_flops #(
        .NumWritePorts(1),
        .NumReadPorts(1),
        .NumFifos(AxiIdCount),
        .Depth(MaxOutstanding),
        .Width(AxiBurstLenWidth),
        .PointerRamReadDataDepthStages(FlopPtrRamRd),
        .DataRamReadDataDepthStages(FlopDataRamRd),
        .RegisterPopOutputs(1),
        // When EnableWlastTracking=0, valid can deassert if downstream_axready deasserts
        .EnableAssertPushValidStability(EnableWlastTracking)
    ) br_fifo_shared_dynamic_flops_req_tracker (
        .clk,
        .rst,
        //
        .push_valid(tracker_fifo_push_valid),
        .push_data(tracker_fifo_push_len),
        .push_ready(tracker_fifo_push_ready),
        .push_fifo_id(tracker_fifo_push_axid),
        .push_full(),
        //
        .pop_valid(tracker_fifo_pop_valid),
        .pop_data(tracker_fifo_pop_len),
        .pop_ready(tracker_fifo_pop_ready),
        .pop_empty(tracker_fifo_pop_empty)
    );
  end

  assign resp_fifo_empty = &tracker_fifo_pop_empty && staging_fifo_pop_empty;

  //
  // Current Response ID
  //
  // Hold the current ID of the burst in progress (in case isolation starts mid-burst). This
  // ID picks the ouptut of the req_tracker FIFO that will be matched up with downstream
  // responses, or used to generate error responses once isolation starts.
  //

  if (SingleIdOnly) begin : gen_single_id_only_resp_info
    assign cur_resp_id = '0;
    assign cur_resp_len = tracker_fifo_pop_len;
    assign cur_resp_valid = tracker_fifo_pop_valid;
    assign tracker_fifo_pop_ready = cur_resp_do_pop;

    `BR_UNUSED(downstream_iso_xid)
    `BR_ASSERT_INTG(single_id_only_resp_info_a,
                    (downstream_iso_xvalid && !isolate_req) |-> (downstream_iso_xid == '0))
    `BR_UNUSED_NAMED(zero_count_unused_resp_info, zero_count)
  end else begin : gen_resp_info
    logic [AxiIdWidth-1:0] cur_resp_id_prev, cur_resp_id_next;
    assign cur_resp_id_next = downstream_iso_xvalid ? downstream_iso_xid : '0;
    assign cur_resp_id = zero_count ? cur_resp_id_next : cur_resp_id_prev;
    // ri lint_check_waive CONST_IF_COND
    `BR_REGL(cur_resp_id_prev, cur_resp_id_next, zero_count && x_beat)

    // Mux the "current" response from the tracker fifo based on the ID received on the downstream.
    br_flow_mux_select_unstable #(
        .NumFlows(AxiIdCount),
        .Width(AxiBurstLenWidth)
    ) br_flow_mux_select_unstable_resp_len (
        .clk,
        .rst,
        //
        .select(cur_resp_id[MinIdWidth-1:0]),
        .push_valid(tracker_fifo_pop_valid),
        .push_data(tracker_fifo_pop_len),
        .push_ready(tracker_fifo_pop_ready),
        //
        .pop_valid_unstable(cur_resp_valid),
        .pop_data_unstable(cur_resp_len),
        .pop_ready(cur_resp_do_pop)
    );
  end

  //
  // Response Beat Counter
  //
  // Counts the number of beats in the burst.
  //

  // First and last beat of the burst.
  assign final_count = resp_beat_count == cur_resp_len;
  assign zero_count = resp_beat_count == '0;

  // Response Beat Counter
  assign x_beat = upstream_xvalid && upstream_xready;

  // The counter resets to 0 on the cycle following the last beat of the burst.
  assign reinit_count = x_beat && final_count;

  // Increment the counter on each beat returned upstream.
  assign incr_count = x_beat;

  if (SingleBeatOnly) begin : gen_single_beat_only_no_counter
    // The beat count is trivially 0 for single-beat bursts.
    assign resp_beat_count = '0;
    `BR_UNUSED(reinit_count)
    `BR_UNUSED(incr_count)
  end else begin : gen_counter
    br_counter_incr #(
        .MaxValue(MaxAxiBurstLen - 1),
        .MaxIncrement(1),
        .EnableSaturate(0),
        .EnableReinitAndIncr(0)
    ) br_counter_incr_resp_beat (
        .clk,
        .rst,
        //
        .reinit(reinit_count),
        .initial_value('0),
        .incr_valid(incr_count),
        .incr(1'b1),
        .value(resp_beat_count),
        .value_next()
    );
  end

  //
  // Response Processing Logic
  //

  // The resp tracker FIFO is popped on the last beat of the burst.
  assign cur_resp_do_pop = x_beat && final_count;

  // The downstream input is popped if tracker FIFO has a matching item and the upstream output
  // is ready.
  assign downstream_iso_xready = cur_resp_valid && upstream_xready;

  // Ignore downstream responses if isolating, use fixed IsolateResp and IsolateData.
  assign downstream_iso_xresp = isolate_req ? IsolateResp : downstream_xresp;
  assign downstream_iso_xdata = isolate_req ? IsolateData : downstream_xdata;

  // When isolating, use the arbiter to pick the next transaction to generate (error) responses
  // for from the resp_tracker FIFO, since there's no downstream responses arriving anymore that
  // would indicate which one to pick.
  assign downstream_iso_xid = isolate_req ? iso_arb_id : downstream_xid;
  assign downstream_iso_xvalid = isolate_req ? iso_any_gnt : downstream_xvalid;

  // When isolating, just accept and discard any arriving downstream responses.
  assign downstream_xready = isolate_req ? 1'b1 : downstream_iso_xready;

  // When isolating, there's no downstream responses arriving. So we just arb over
  // the resp_tracker FIFO to get the next transaction to generate (error) responses
  // for.

  if (SingleIdOnly) begin : gen_single_id_only_no_arbiter
    assign iso_arb_id = '0;
    `BR_UNUSED_NAMED(zero_count_unused_arbiter, zero_count)
  end else begin : gen_arbiter
    logic [AxiIdCount-1:0] tracker_fifo_pop_iso_gnt;
    logic [AxiIdCount-1:0] tracker_fifo_pop_iso_gnt_prev;
    logic [AxiIdCount-1:0] tracker_fifo_pop_iso_gnt_cur;

    logic iso_arb_accept;

    // Arbiter state is advanced on zero_count where a response is accepted upstream.
    assign iso_arb_accept = isolate_req && x_beat && zero_count;

    br_arb_rr #(
        .NumRequesters(AxiIdCount)
    ) br_arb_rr_iso_req (
        .clk,
        .rst,
        //
        .request(tracker_fifo_pop_valid),
        .grant(tracker_fifo_pop_iso_gnt_cur),
        .enable_priority_update(iso_arb_accept)
    );

    // Grant is held through the end of the burst.
    `BR_REGL(tracker_fifo_pop_iso_gnt_prev, tracker_fifo_pop_iso_gnt_cur, iso_arb_accept)
    assign tracker_fifo_pop_iso_gnt = zero_count ? tracker_fifo_pop_iso_gnt_cur :
                                     tracker_fifo_pop_iso_gnt_prev;

    br_enc_onehot2bin #(
        .NumValues(AxiIdCount),
        .BinWidth (AxiIdWidth)
    ) br_enc_onehot2bin_iso_req (
        .clk,
        .rst,
        //
        .in(tracker_fifo_pop_iso_gnt),
        .out(iso_arb_id),
        .out_valid()
    );
  end

  assign iso_any_gnt = |tracker_fifo_pop_valid;

  //
  // Output Assignment
  //

  // The last beat of the burst is asserted when the counter matches the
  // current burst length.
  assign upstream_xlast = final_count;

  // Output valid if a downstream response is valid and the tracker fifo has something on the
  // output corresponding to the ID of the downstream response.
  assign upstream_xvalid = downstream_iso_xvalid && cur_resp_valid;

  assign upstream_xid = cur_resp_id;
  assign upstream_xresp = downstream_iso_xresp;
  assign upstream_xdata = downstream_iso_xdata;

  assign upstream_axready = downstream_axready && staging_fifo_push_ready && can_accept_new_req;
  assign downstream_axvalid = upstream_axvalid && staging_fifo_push_ready && can_accept_new_req;
  assign downstream_axid = upstream_axid;
  assign downstream_axlen = upstream_axlen;

  //
  // Assertions
  //

  // Check that the downstream last beat matches the one generated by the counter
  // (unless isolating).
  `BR_ASSERT_IMPL(xlast_match_a,
                  (upstream_xvalid && !isolate_req) |-> downstream_xlast == upstream_xlast)
  `BR_UNUSED(downstream_xlast)

  // Check that downstream ID matches the registered copy (i.e. no burst interleave allowed)
  `BR_ASSERT_IMPL(id_match_a, (upstream_xvalid && !isolate_req) |-> downstream_xid == upstream_xid)
endmodule : br_amba_iso_resp_tracker
