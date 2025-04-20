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
    localparam int AxiBurstLenWidth = MaxAxiBurstLen == 1 ? 1 : $clog2(MaxAxiBurstLen)
) (
    input logic clk,
    input logic rst,
    // AW or AR channel from upstream
    output logic upstream_axready,
    input logic upstream_axvalid,
    input logic [AxiIdWidth-1:0] upstream_axid,
    input logic [AxiBurstLenWidth-1:0] upstream_axlen,
    // R or B channel to upstream
    input logic upstream_xready,
    output logic upstream_xvalid,
    output logic [AxiIdWidth-1:0] upstream_xid,
    output br_amba::axi_resp_t upstream_xresp,
    output logic upstream_xlast,
    output logic [DataWidth-1:0] upstream_xdata,
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
  `BR_ASSERT_STATIC(max_axi_burst_len_1_or_amba_a,
                    MaxAxiBurstLen == 1 || MaxAxiBurstLen == 2 ** br_amba::AxiBurstLenWidth)
  `BR_ASSERT_STATIC(axi_id_width_gte_clog2_a, AxiIdWidth >= $clog2(AxiIdCount))
  `BR_ASSERT_INTG(axlen_legal_range_a, upstream_axvalid |-> upstream_axlen < MaxAxiBurstLen)
  // Check that the isolate request can only fall when the tracker is empty and the upstream
  // is not driving a new request (because it is held off outside of this module).
  `BR_ASSERT_INTG(legal_request_fall_a, $fell(isolate_req) |-> $past(resp_fifo_empty) && !$past
                                        (upstream_axvalid))

  // Local parameters
  localparam bit SingleBeatOnly = (MaxAxiBurstLen == 1);
  localparam bit SingleIdOnly = (AxiIdCount == 1);
  localparam int MinIdWidth = (AxiIdCount == 1) ? 1 : $clog2(AxiIdCount);

  // Local signals
  logic [AxiBurstLenWidth-1:0] ax_beat_len;
  logic [MinIdWidth-1:0] ax_id;
  logic ax_beat;
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

  //
  // Per-ID Request Tracker FIFO
  // Stores ordered list of request lengths for each ID.
  //

  assign ax_beat_len = SingleBeatOnly ? 1'b0 : upstream_axlen;
  assign ax_id = SingleIdOnly ? '0 : upstream_axid[MinIdWidth-1:0];
  assign ax_beat = upstream_axvalid && upstream_axready;

  if (MinIdWidth < AxiIdWidth) begin : gen_id_width_lt_len_width
    `BR_UNUSED_NAMED(upstream_axid_unused, upstream_axid[AxiIdWidth-1:MinIdWidth])
    `BR_ASSERT(unused_upper_axid_zero_a,
               upstream_axvalid |-> upstream_axid[AxiIdWidth-1:MinIdWidth] == '0)
  end

  logic [AxiIdCount-1:0] tracker_fifo_pop_empty;

  if (SingleIdOnly) begin : gen_single_fifo
    br_fifo_flops #(
        .Depth(MaxOutstanding),
        .Width(AxiBurstLenWidth),
        .EnableBypass(1),
        .RegisterPopOutputs(1)
    ) br_fifo_flops_req_tracker (
        .clk,
        .rst,
        //
        .push_valid(ax_beat),
        .push_data(ax_beat_len),
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
    `BR_UNUSED(ax_id)
  end else begin : gen_multi_fifo
    br_fifo_shared_dynamic_flops #(
        .NumWritePorts(1),
        .NumReadPorts(1),
        .NumFifos(AxiIdCount),
        .Depth(MaxOutstanding),
        .Width(AxiBurstLenWidth),
        .PointerRamReadDataDepthStages(FlopPtrRamRd),
        .DataRamReadDataDepthStages(FlopDataRamRd),
        .RegisterPopOutputs(1)
    ) br_fifo_shared_dynamic_flops_req_tracker (
        .clk,
        .rst,
        //
        .push_valid(ax_beat),
        .push_data(ax_beat_len),
        .push_ready(tracker_fifo_push_ready),
        .push_fifo_id(ax_id),
        .push_full(),
        //
        .pop_valid(tracker_fifo_pop_valid),
        .pop_data(tracker_fifo_pop_len),
        .pop_ready(tracker_fifo_pop_ready),
        .pop_empty(tracker_fifo_pop_empty)
    );
  end

  assign resp_fifo_empty = &tracker_fifo_pop_empty;


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
    `BR_ASSERT(single_id_only_resp_info_a,
               (downstream_iso_xvalid && !isolate_req) |-> (downstream_iso_xid == '0))
    `BR_UNUSED_NAMED(zero_count_unused_resp_info, zero_count)
  end else begin : gen_resp_info
    logic [AxiIdWidth-1:0] cur_resp_id_last, cur_resp_id_next;
    assign cur_resp_id_next = downstream_iso_xid;
    assign cur_resp_id = zero_count ? cur_resp_id_next : cur_resp_id_last;
    // ri lint_check_waive CONST_IF_COND
    `BR_REGL(cur_resp_id_last, cur_resp_id_next, zero_count)

    // Mux the "current" response from the tracker fifo based on the ID received on the downstream.
    br_mux_bin #(
        .NumSymbolsIn(AxiIdCount),
        .SymbolWidth (AxiBurstLenWidth),
        .SelectWidth (AxiIdWidth)
    ) br_mux_bin_resp_len (
        .select(cur_resp_id),
        .in(tracker_fifo_pop_len),
        .out(cur_resp_len),
        .out_valid()
    );

    br_mux_bin #(
        .NumSymbolsIn(AxiIdCount),
        .SymbolWidth (1),
        .SelectWidth (AxiIdWidth)
    ) br_mux_bin_resp_valid (
        .select(cur_resp_id),
        .in(tracker_fifo_pop_valid),
        .out(cur_resp_valid),
        .out_valid()
    );

    br_enc_bin2onehot #(
        .NumValues(AxiIdCount),
        .BinWidth (AxiIdWidth)
    ) br_enc_bin2onehot_resp_ready (
        .clk,
        .rst,
        //
        .in(cur_resp_id),
        .in_valid(cur_resp_do_pop),
        .out(tracker_fifo_pop_ready)
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
        .grant(tracker_fifo_pop_iso_gnt),
        .enable_priority_update(iso_arb_accept)
    );

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

  assign upstream_axready = tracker_fifo_push_ready;

  //
  // Assertions
  //

  // Check that the downstream last beat matches the one generated by the counter
  // (unless isolating).
  `BR_ASSERT(xlast_match_a,
             (upstream_xvalid && !isolate_req) |-> downstream_xlast == upstream_xlast)
  `BR_UNUSED(downstream_xlast)

  // Check that downstream ID matches the registered copy (i.e. no burst interleave allowed)
  `BR_ASSERT(id_match_a, (upstream_xvalid && !isolate_req) |-> downstream_xid == upstream_xid)
endmodule : br_amba_iso_resp_tracker
