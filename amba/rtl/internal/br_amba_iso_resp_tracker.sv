// SPDX-License-Identifier: Apache-2.0

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
    // Set to 1 to use a dynamic storage shared FIFO for the tracking list.
    parameter bit UseDynamicFifo = 1,
    // Number of pipeline stages to use for the pointer RAM read data.
    parameter int DynamicFifoPointerRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the data RAM read data.
    parameter int DynamicFifoDataRamReadDataDepthStages = 0,
    // Number of pipeline stages to use for the pointer RAM address.
    parameter int DynamicFifoPointerRamAddressDepthStages = 1,
    // Number of pipeline stages to use for the data RAM address.
    parameter int DynamicFifoDataRamAddressDepthStages = 1,
    // Number of linked lists per FIFO.
    parameter int DynamicFifoNumLinkedListsPerFifo = 2,
    // Number of pipeline stages to use for the staging buffer.
    parameter int DynamicFifoStagingBufferDepth = 2,
    // Number of pipeline stages to use for the pop outputs.
    parameter int DynamicFifoRegisterPopOutputs = 1,
    // Number of pipeline stages to use for the deallocation.
    parameter int DynamicFifoRegisterDeallocation = 1,
    // When UseDynamicFifo=0, this parameter controls the depth of the Per-ID
    // tracking FIFO.
    parameter int PerIdFifoDepth = 2,
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
  if (UseDynamicFifo || SingleIdOnly) begin : gen_total_req_count
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
    assign can_accept_new_req = total_req_count < MaxOutstanding;
  end else begin : gen_total_req_count_per_id
    // With static FIFOs, since storage is not shared, need to count total requests per ID to ensure
    // that all accepted requests can eventually sink into a (per-ID) tracker FIFO.
    logic [AxiIdCount-1:0][$clog2(PerIdFifoDepth+1)-1:0] total_req_count;
    logic [AxiIdCount-1:0] can_accept_new_req_per_id;

    for (genvar i = 0; i < AxiIdCount; i++) begin : gen_counter_per_id
      logic incr_valid;

      assign incr_valid = staging_fifo_push_valid
                          && staging_fifo_push_ready
                          && (upstream_axid == i);

      br_counter #(
          .MaxValue(PerIdFifoDepth),
          .MaxChange(1),
          .EnableWrap(0),
          .EnableSaturate(0),
          .EnableReinitAndChange(0)
      ) br_counter_total_req_per_id (
          .clk,
          .rst,
          //
          .reinit(1'b0),
          .initial_value('0),
          .incr_valid(incr_valid),
          .incr(1'b1),
          .decr_valid(tracker_fifo_pop_valid[i] && tracker_fifo_pop_ready[i]),
          .decr(1'b1),
          .value(total_req_count[i]),
          .value_next()
      );
      assign can_accept_new_req_per_id[i] = total_req_count[i] < PerIdFifoDepth;
    end

    logic [MinIdWidth-1:0] can_accept_new_req_mux_select;
    assign can_accept_new_req_mux_select = upstream_axvalid ? upstream_axid[MinIdWidth-1:0] : '0;

    br_mux_bin #(
        .NumSymbolsIn(AxiIdCount),
        .SymbolWidth (1)
    ) br_mux_bin_can_accept_new_req (
        .select(can_accept_new_req_mux_select),
        .in(can_accept_new_req_per_id),
        .out(can_accept_new_req),
        .out_valid()
    );
  end

  if (EnableWlastTracking) begin : gen_wlast_tracking
    logic staging_fifo_pop_valid;
    logic staging_fifo_pop_ready;
    logic wlast_fifo_pop_valid;
    logic wlast_fifo_pop_ready;
    logic wlast_fifo_push_valid;
    logic wlast_fifo_push_valid_is_last;
    logic wlast_fifo_push_ready;

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
        .pop_ready({downstream_wready, wlast_fifo_push_ready})
    );

    assign wlast_fifo_push_valid_is_last = wlast_fifo_push_valid && upstream_wlast;

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

  end else begin : gen_no_wlast_tracking
    assign upstream_wready = 1'b0;
    `BR_UNUSED(upstream_wvalid)
    `BR_UNUSED(upstream_wlast)
    assign downstream_wlast  = 1'b0;
    assign downstream_wvalid = 1'b0;
    `BR_UNUSED(downstream_wready)

    assign tracker_fifo_push_valid = staging_fifo_push_valid;
    assign tracker_fifo_push_len   = staging_fifo_push_len;
    assign tracker_fifo_push_axid  = staging_fifo_push_axid;
    assign staging_fifo_push_ready = tracker_fifo_push_ready;
    assign staging_fifo_pop_empty  = 1'b1;
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
    if (UseDynamicFifo) begin : gen_dynamic_fifo
      br_fifo_shared_dynamic_flops #(
          .NumWritePorts(1),
          .NumReadPorts(1),
          .NumFifos(AxiIdCount),
          .Depth(MaxOutstanding),
          .Width(AxiBurstLenWidth),
          .PointerRamReadDataDepthStages(DynamicFifoPointerRamReadDataDepthStages),
          .PointerRamAddressDepthStages(DynamicFifoPointerRamAddressDepthStages),
          .NumLinkedListsPerFifo(DynamicFifoNumLinkedListsPerFifo),
          .DataRamReadDataDepthStages(DynamicFifoDataRamReadDataDepthStages),
          .DataRamAddressDepthStages(DynamicFifoDataRamAddressDepthStages),
          .StagingBufferDepth(DynamicFifoStagingBufferDepth),
          .RegisterPopOutputs(DynamicFifoRegisterPopOutputs),
          .RegisterDeallocation(DynamicFifoRegisterDeallocation),
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
    end else begin : gen_static_fifo
      logic [AxiIdCount-1:0] static_fifo_push_valid;
      logic [AxiIdCount-1:0] static_fifo_push_ready;
      logic [AxiIdCount-1:0][AxiBurstLenWidth-1:0] static_fifo_push_data;
      logic [MinIdWidth-1:0] static_fifo_mux_select;

      assign static_fifo_mux_select = tracker_fifo_push_valid ? tracker_fifo_push_axid : '0;

      br_flow_demux_select_unstable #(
          .NumFlows(AxiIdCount),
          .Width(AxiBurstLenWidth),
          // When EnableWlastTracking=0, valid can deassert if downstream_axready deasserts
          .EnableAssertPushValidStability(EnableWlastTracking)
      ) br_flow_demux_select_unstable_req_tracker (
          .clk,
          .rst,
          //
          .select(static_fifo_mux_select),
          //
          .push_valid(tracker_fifo_push_valid),
          .push_data(tracker_fifo_push_len),
          .push_ready(tracker_fifo_push_ready),
          //
          .pop_valid_unstable(static_fifo_push_valid),
          .pop_data_unstable(static_fifo_push_data),
          .pop_ready(static_fifo_push_ready)
      );

      for (genvar i = 0; i < AxiIdCount; i++) begin : gen_fifo_per_id
        if (SingleBeatOnly) begin : gen_single_beat_only_per_id
          // In static FIFO mode, when SingleBeatOnly=1, the FIFO doesn't need to store anything.
          // So we can replace it with a counter.
          logic [$clog2(PerIdFifoDepth+1)-1:0] tracked_count_per_id;

          br_counter #(
              .MaxValue(PerIdFifoDepth),
              .MaxChange(1),
              .EnableWrap(0),
              .EnableSaturate(0),
              .EnableReinitAndChange(0)
          ) br_counter_tracked_count_per_id (
              .clk,
              .rst,
              //
              .reinit(1'b0),
              .initial_value('0),
              .incr_valid(static_fifo_push_valid[i] && static_fifo_push_ready[i]),
              .incr(1'b1),
              .decr_valid(tracker_fifo_pop_valid[i] && tracker_fifo_pop_ready[i]),
              .decr(1'b1),
              .value(tracked_count_per_id),
              .value_next()
          );

          assign static_fifo_push_ready[i] = tracked_count_per_id < PerIdFifoDepth;
          assign tracker_fifo_pop_valid[i] = tracked_count_per_id > 0;
          assign tracker_fifo_pop_empty[i] = tracked_count_per_id == 0;
          assign tracker_fifo_pop_len[i]   = '0;
          `BR_UNUSED_NAMED(static_fifo_push_data_unused, static_fifo_push_data[i])
        end else begin : gen_multi_beat_per_id
          br_fifo_flops #(
              .Depth(PerIdFifoDepth),
              .Width(AxiBurstLenWidth),
              .EnableBypass(0),
              .RegisterPopOutputs(0),
              // When EnableWlastTracking=0, valid can deassert if downstream_axready deasserts
              .EnableAssertPushValidStability(EnableWlastTracking)
          ) br_fifo_flops_req_tracker (
              .clk,
              .rst,
              //
              .push_valid(static_fifo_push_valid[i]),
              .push_data(static_fifo_push_data[i]),
              .push_ready(static_fifo_push_ready[i]),
              //
              .pop_valid(tracker_fifo_pop_valid[i]),
              .pop_data(tracker_fifo_pop_len[i]),
              .pop_ready(tracker_fifo_pop_ready[i]),
              //
              .full(),
              .full_next(),
              .slots(),
              .slots_next(),
              .empty(tracker_fifo_pop_empty[i]),
              .empty_next(),
              .items(),
              .items_next()
          );
        end
      end
    end
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

  always_comb begin
    if (isolate_req) begin
      // Ignore downstream responses if isolating, use fixed IsolateResp and IsolateData.
      downstream_iso_xresp = IsolateResp;
      downstream_iso_xdata = IsolateData;
      // When isolating, use the arbiter to pick the next transaction to generate (error) responses
      // for from the resp_tracker FIFO, since there's no downstream responses arriving anymore that
      // would indicate which one to pick.
      downstream_iso_xid = iso_arb_id;
      downstream_iso_xvalid = iso_any_gnt;
      // When isolating, just accept and discard any arriving downstream responses.
      downstream_xready = 1'b1;
    end else begin
      downstream_iso_xresp = downstream_xresp;
      downstream_iso_xdata = downstream_xdata;
      downstream_iso_xid = downstream_xid;
      downstream_iso_xvalid = downstream_xvalid;
      downstream_xready = downstream_iso_xready;
    end
  end

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

    // Break up timing path from arbiter -> FIFO pop.
    // Note this simple flop stage causes a 1-cycle bubble between bursts with different IDs
    // when isolating and generating fake responses. But isolation is not performance critical,
    // so this is acceptable.
    logic [AxiIdCount-1:0] tracker_fifo_pop_iso_gnt_flopped;
    `BR_REG(tracker_fifo_pop_iso_gnt_flopped, tracker_fifo_pop_iso_gnt)

    br_enc_onehot2bin #(
        .NumValues(AxiIdCount),
        .BinWidth (AxiIdWidth)
    ) br_enc_onehot2bin_iso_req (
        .clk,
        .rst,
        //
        .in(tracker_fifo_pop_iso_gnt_flopped),
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
