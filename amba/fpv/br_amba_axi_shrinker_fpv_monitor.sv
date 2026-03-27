// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL AXI4 Shrinker FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_amba_axi_shrinker_fpv_monitor #(
    parameter int AddrWidth = 12,
    parameter int WideDataWidth = 16,
    parameter int NarrowDataWidth = 8,
    parameter int IdWidth = 1,
    parameter int AWUserWidth = 1,
    parameter int ARUserWidth = 1,
    parameter int WUserWidth = 1,
    parameter int BUserWidth = 1,
    parameter int RUserWidth = 1,
    parameter int MaxOutstandingReqs = 1,
    parameter int WriteFifoDepth = 1,
    parameter bit RegisterNarrowOutputs = 1,
    parameter bit RegisterWideOutputs = 1,
    localparam int WideStrobeWidth = WideDataWidth / 8,
    localparam int NarrowStrobeWidth = NarrowDataWidth / 8
) (
    input clk,
    input rst,  // Synchronous, active-high reset

    // Wide AXI4 target interface
    input logic [                 AddrWidth-1:0] wide_awaddr,
    input logic [                   IdWidth-1:0] wide_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] wide_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] wide_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] wide_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] wide_awprot,
    input logic [               AWUserWidth-1:0] wide_awuser,
    input logic                                  wide_awvalid,
    input logic                                  wide_awready,
    input logic [             WideDataWidth-1:0] wide_wdata,
    input logic [           WideStrobeWidth-1:0] wide_wstrb,
    input logic [                WUserWidth-1:0] wide_wuser,
    input logic                                  wide_wlast,
    input logic                                  wide_wvalid,
    input logic                                  wide_wready,
    input logic [                   IdWidth-1:0] wide_bid,
    input logic [                BUserWidth-1:0] wide_buser,
    input logic [     br_amba::AxiRespWidth-1:0] wide_bresp,
    input logic                                  wide_bvalid,
    input logic                                  wide_bready,
    input logic [                 AddrWidth-1:0] wide_araddr,
    input logic [                   IdWidth-1:0] wide_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] wide_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] wide_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] wide_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] wide_arprot,
    input logic [               ARUserWidth-1:0] wide_aruser,
    input logic                                  wide_arvalid,
    input logic                                  wide_arready,
    input logic [                   IdWidth-1:0] wide_rid,
    input logic [             WideDataWidth-1:0] wide_rdata,
    input logic [                RUserWidth-1:0] wide_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] wide_rresp,
    input logic                                  wide_rlast,
    input logic                                  wide_rvalid,
    input logic                                  wide_rready,

    // Narrow AXI4 initiator interface
    input logic [                 AddrWidth-1:0] narrow_awaddr,
    input logic [                   IdWidth-1:0] narrow_awid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] narrow_awlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] narrow_awsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] narrow_awburst,
    input logic [     br_amba::AxiProtWidth-1:0] narrow_awprot,
    input logic [               AWUserWidth-1:0] narrow_awuser,
    input logic                                  narrow_awvalid,
    input logic                                  narrow_awready,
    input logic [           NarrowDataWidth-1:0] narrow_wdata,
    input logic [         NarrowStrobeWidth-1:0] narrow_wstrb,
    input logic [                WUserWidth-1:0] narrow_wuser,
    input logic                                  narrow_wlast,
    input logic                                  narrow_wvalid,
    input logic                                  narrow_wready,
    input logic [                   IdWidth-1:0] narrow_bid,
    input logic [                BUserWidth-1:0] narrow_buser,
    input logic [     br_amba::AxiRespWidth-1:0] narrow_bresp,
    input logic                                  narrow_bvalid,
    input logic                                  narrow_bready,
    input logic [                 AddrWidth-1:0] narrow_araddr,
    input logic [                   IdWidth-1:0] narrow_arid,
    input logic [ br_amba::AxiBurstLenWidth-1:0] narrow_arlen,
    input logic [br_amba::AxiBurstSizeWidth-1:0] narrow_arsize,
    input logic [br_amba::AxiBurstTypeWidth-1:0] narrow_arburst,
    input logic [     br_amba::AxiProtWidth-1:0] narrow_arprot,
    input logic [               ARUserWidth-1:0] narrow_aruser,
    input logic                                  narrow_arvalid,
    input logic                                  narrow_arready,
    input logic [                   IdWidth-1:0] narrow_rid,
    input logic [           NarrowDataWidth-1:0] narrow_rdata,
    input logic [                RUserWidth-1:0] narrow_ruser,
    input logic [     br_amba::AxiRespWidth-1:0] narrow_rresp,
    input logic                                  narrow_rlast,
    input logic                                  narrow_rvalid,
    input logic                                  narrow_rready
);

  localparam int WideSizeLog2 = $clog2(WideStrobeWidth);
  localparam int NarrowSizeLog2 = $clog2(NarrowStrobeWidth);
  localparam int LanesPerWide = WideDataWidth / NarrowDataWidth;
  localparam int LaneIdxWidth = br_math::clamped_clog2(LanesPerWide);
  localparam int ByteOffsetWidth = br_math::clamped_clog2(WideStrobeWidth);
  localparam int InternalIdWidth = br_math::clamped_clog2(MaxOutstandingReqs);
  localparam int BeatOffsetIncrWidth = $clog2(NarrowStrobeWidth + 1);
  localparam int BeatsPerWideWidth = br_math::clamped_clog2(LanesPerWide + 1);
  localparam int RespRankWidth = 2;
  typedef struct packed {
    logic is_fixed;
    logic [ByteOffsetWidth-1:0] offset;
    logic [BeatOffsetIncrWidth-1:0] offset_incr;
    logic [BeatsPerWideWidth-1:0] beats_per_wide;
  } fv_w_ctx_t;
  localparam int AwPayloadWidth = AddrWidth + IdWidth + br_amba::AxiBurstLenWidth +
                                  br_amba::AxiBurstSizeWidth + br_amba::AxiBurstTypeWidth +
                                  br_amba::AxiProtWidth + AWUserWidth;
  localparam int ArPayloadWidth = AddrWidth + IdWidth + br_amba::AxiBurstLenWidth +
                                  br_amba::AxiBurstSizeWidth + br_amba::AxiBurstTypeWidth +
                                  br_amba::AxiProtWidth + ARUserWidth;
  localparam int BPayloadWidth = IdWidth + BUserWidth + br_amba::AxiRespWidth;
  localparam int WPayloadWidth = NarrowDataWidth + NarrowStrobeWidth + WUserWidth + 1;
  localparam int RPayloadWidth = IdWidth + WideDataWidth + RUserWidth + br_amba::AxiRespWidth + 1;
  localparam int WFifoPayloadWidth = $bits(fv_w_ctx_t);

  // ABVIP should send more than DUT to test backpressure.
  localparam int MaxPending = MaxOutstandingReqs + WriteFifoDepth + 2;
  localparam int WriteMaxPending = MaxOutstandingReqs + WriteFifoDepth;

  logic [br_amba::AxiBurstSizeWidth-1:0] fv_narrow_arsize;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_narrow_arlen;
  logic [ArPayloadWidth-1:0] fv_narrow_ar_payload;
  logic [br_amba::AxiBurstSizeWidth-1:0] fv_narrow_awsize;
  logic [br_amba::AxiBurstLenWidth-1:0] fv_narrow_awlen;
  logic [AwPayloadWidth-1:0] fv_narrow_aw_payload;
  int unsigned aw_shift;
  int unsigned ar_shift;
  logic [br_amba::AxiBurstLenWidth:0] fv_narrow_awlen_ext;
  logic [br_amba::AxiBurstLenWidth:0] fv_narrow_arlen_ext;
  logic fv_narrow_w_hs;
  logic fv_wide_ar_hs;
  logic fv_narrow_r_hs;
  logic fv_wide_rdata_vld;
  logic fv_wide_w_hs;
  logic fv_w_fifo_push;
  logic fv_w_fifo_empty;
  fv_w_ctx_t fv_w_fifo_push_ctx;
  logic [WFifoPayloadWidth-1:0] fv_w_fifo_push_data;
  fv_w_ctx_t fv_w_fifo_pop_ctx;
  logic [WFifoPayloadWidth-1:0] fv_w_fifo_pop_data;
  logic fv_w_active_load;
  logic fv_w_active_valid;
  logic fv_w_active_done;
  logic fv_w_ctx_valid;
  logic [BeatOffsetIncrWidth-1:0] fv_w_offset_incr_cfg;
  logic [BeatsPerWideWidth-1:0] fv_w_beats_per_wide_cfg;
  fv_w_ctx_t fv_w_active_ctx;
  logic [ByteOffsetWidth-1:0] fv_w_active_offset_next;
  fv_w_ctx_t fv_w_ctx;
  logic fv_w_beat_start;
  logic [ByteOffsetWidth-1:0] fv_w_offset_after_wide_beat;
  logic [LanesPerWide-1:0] fv_narrow_w_pred_vld;
  logic [LanesPerWide-1:0][WPayloadWidth-1:0] fv_narrow_w_pred_payloads;
  logic [InternalIdWidth-1:0] fv_rid_idx;
  logic [ByteOffsetWidth-1:0] fv_wide_ar_offset;
  logic [BeatOffsetIncrWidth-1:0] fv_r_offset_incr_cfg;
  logic [LaneIdxWidth-1:0] fv_r_lane_cur;
  logic [ByteOffsetWidth-1:0] fv_r_offset_after_beat;
  logic [BeatsPerWideWidth-1:0] fv_r_beats_per_wide_cfg;
  logic fv_r_beat_done;
  logic [br_amba::AxiRespWidth-1:0] fv_wide_rresp_cur;
  logic [RespRankWidth-1:0] fv_wide_rresp_rank_cur;
  logic [RespRankWidth-1:0] fv_r_resp_rank_next;
  // Per-slot state for the abstract wide-R reconstruction model.
  logic [MaxOutstandingReqs-1:0] fv_r_is_fixed;
  logic [MaxOutstandingReqs-1:0] fv_r_is_fixed_next;
  logic [MaxOutstandingReqs-1:0][ByteOffsetWidth-1:0] fv_r_offset;
  logic [MaxOutstandingReqs-1:0][ByteOffsetWidth-1:0] fv_r_offset_next;
  logic [MaxOutstandingReqs-1:0][BeatOffsetIncrWidth-1:0] fv_r_offset_incr;
  logic [MaxOutstandingReqs-1:0][BeatOffsetIncrWidth-1:0] fv_r_offset_incr_next;
  logic [MaxOutstandingReqs-1:0][BeatsPerWideWidth-1:0] fv_r_beats_per_wide;
  logic [MaxOutstandingReqs-1:0][BeatsPerWideWidth-1:0] fv_r_beats_per_wide_next;
  logic [MaxOutstandingReqs-1:0][BeatsPerWideWidth-1:0] fv_r_beats_remaining;
  logic [MaxOutstandingReqs-1:0][BeatsPerWideWidth-1:0] fv_r_beats_remaining_next;
  logic [MaxOutstandingReqs-1:0][WideDataWidth-1:0] fv_wide_rdata_saved;
  logic [MaxOutstandingReqs-1:0][WideDataWidth-1:0] fv_wide_rdata_saved_next;
  logic [WideDataWidth-1:0] fv_wide_rdata_cur;
  logic [MaxOutstandingReqs-1:0][RespRankWidth-1:0] fv_wide_rresp_rank_saved;
  logic [MaxOutstandingReqs-1:0][RespRankWidth-1:0] fv_wide_rresp_rank_saved_next;
  logic [RPayloadWidth-1:0] fv_wide_r_payload;

  // Rank narrow responses by architectural severity while building a wide beat.
  function automatic logic [RespRankWidth-1:0] fv_resp_rank(
      input logic [br_amba::AxiRespWidth-1:0] resp);
    begin
      unique case (br_amba::axi_resp_t'(resp))
        br_amba::AxiRespOkay: fv_resp_rank = 2'd0;
        br_amba::AxiRespExOkay: fv_resp_rank = 2'd1;
        br_amba::AxiRespSlverr: fv_resp_rank = 2'd2;
        br_amba::AxiRespDecerr: fv_resp_rank = 2'd3;
        default: fv_resp_rank = 'x;
      endcase
    end
  endfunction

  // Convert the saved worst-severity rank back into the AXI response encoding
  // expected on the reconstructed wide R channel.
  function automatic logic [br_amba::AxiRespWidth-1:0] fv_rank_resp(
      input logic [RespRankWidth-1:0] rank);
    begin
      unique case (rank)
        2'd0: fv_rank_resp = br_amba::AxiRespOkay;
        2'd1: fv_rank_resp = br_amba::AxiRespExOkay;
        2'd2: fv_rank_resp = br_amba::AxiRespSlverr;
        2'd3: fv_rank_resp = br_amba::AxiRespDecerr;
        default: fv_rank_resp = 'x;
      endcase
    end
  endfunction

  // ----------FV assumptions----------
  `BR_ASSUME(
      shrinking_awburst_incr_a,
      (wide_awvalid && wide_awsize > NarrowSizeLog2) |-> wide_awburst == br_amba::AxiBurstIncr)
  `BR_ASSUME(
      shrinking_arburst_incr_a,
      (wide_arvalid && wide_arsize > NarrowSizeLog2) |-> wide_arburst == br_amba::AxiBurstIncr)

  // Make sure wide len and size won't result in narrow len overflowing
  localparam int ExtBurstLenWidth = br_amba::AxiBurstLenWidth + WideSizeLog2 - NarrowSizeLog2;
  localparam int MaxBurstLen = 2 ** br_amba::AxiBurstLenWidth - 1;

  logic [ExtBurstLenWidth-1:0] ext_wide_awlen;
  logic [ExtBurstLenWidth-1:0] ext_wide_arlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_awlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_arlen;

  assign ext_wide_awlen = ExtBurstLenWidth'(wide_awlen);
  assign ext_wide_arlen = ExtBurstLenWidth'(wide_arlen);

  assign ext_narrow_awlen =
      (wide_awsize > NarrowSizeLog2) ?
      ((ext_wide_awlen + 1'b1) << (wide_awsize - NarrowSizeLog2)) - 1'b1 : ext_wide_awlen;
  assign ext_narrow_arlen =
      (wide_arsize > NarrowSizeLog2) ?
      ((ext_wide_arlen + 1'b1) << (wide_arsize - NarrowSizeLog2)) - 1'b1 : ext_wide_arlen;

  `BR_ASSUME(narrow_awlen_no_overflow_a, wide_awvalid |-> ext_narrow_awlen <= MaxBurstLen)
  `BR_ASSUME(narrow_arlen_no_overflow_a, wide_arvalid |-> ext_narrow_arlen <= MaxBurstLen)

  // ----------Shrink checks----------
  // ----------AR channel----------
  always_comb begin
    ar_shift = 0;
    fv_narrow_arsize = wide_arsize;

    if (wide_arsize > NarrowSizeLog2) begin
      fv_narrow_arsize = NarrowSizeLog2;
      ar_shift = wide_arsize - NarrowSizeLog2;
    end

    // AXI len encodes beats - 1, so after scaling the beat count by the width ratio
    // we subtract 1 to convert back to the AXI burst-length encoding.
    fv_narrow_arlen_ext = (({1'b0, wide_arlen} + 1'b1) << ar_shift) - 1'b1;
    fv_narrow_arlen = fv_narrow_arlen_ext[br_amba::AxiBurstLenWidth-1:0];
  end

  assign fv_narrow_ar_payload = {
    wide_araddr,
    wide_arid,
    fv_narrow_arlen,
    fv_narrow_arsize,
    wide_arburst,
    wide_arprot,
    wide_aruser
  };

  // Checks that the RTL narrow AR channel matches the monitor prediction for
  // narrow arlen/arsize derived from each accepted wide AR request.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(ArPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxOutstandingReqs)
  ) ar_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(wide_arvalid && wide_arready),
      .incoming_data(fv_narrow_ar_payload),
      .outgoing_vld(narrow_arvalid && narrow_arready),
      .outgoing_data({
        narrow_araddr,
        narrow_arid,
        narrow_arlen,
        narrow_arsize,
        narrow_arburst,
        narrow_arprot,
        narrow_aruser
      })
  );

  // ----------R channel----------
  // Abstract reconstruction model for wide R beats. Each accepted AR seeds the
  // slot's byte offset, narrow-beat stride, and the number of narrow beats that
  // must be seen before the next wide beat is expected on the output.
  assign fv_wide_ar_hs = wide_arvalid && wide_arready;
  assign fv_narrow_r_hs = narrow_rvalid && narrow_rready;
  assign fv_rid_idx = narrow_rid[InternalIdWidth-1:0];
  assign fv_wide_ar_offset = wide_araddr[ByteOffsetWidth-1:0];
  // A wide beat is formed from 2**(wide_arsize - narrow_arsize) narrow beats.
  assign fv_r_offset_incr_cfg = BeatOffsetIncrWidth'(1'b1) << fv_narrow_arsize;
  assign fv_r_beats_per_wide_cfg = BeatsPerWideWidth'(1'b1) << ar_shift;
  // The current byte offset determines which narrow lane is being filled next.
  assign fv_r_lane_cur = LaneIdxWidth'(fv_r_offset[fv_rid_idx] >> NarrowSizeLog2);
  assign fv_r_offset_after_beat = fv_r_is_fixed[fv_rid_idx] ? fv_r_offset[fv_rid_idx]
                                                            : fv_r_offset[fv_rid_idx] +
                                                              fv_r_offset_incr[fv_rid_idx];
  assign fv_r_beat_done = fv_r_beats_remaining[fv_rid_idx] == BeatsPerWideWidth'(1);
  assign fv_wide_rdata_vld = fv_narrow_r_hs && fv_r_beat_done;
  assign fv_r_resp_rank_next = (fv_wide_rresp_rank_saved[fv_rid_idx] >= fv_resp_rank(
      narrow_rresp
  )) ? fv_wide_rresp_rank_saved[fv_rid_idx] : fv_resp_rank(
      narrow_rresp
  );

  always_comb begin
    fv_r_is_fixed_next = fv_r_is_fixed;
    fv_r_offset_next = fv_r_offset;
    fv_r_offset_incr_next = fv_r_offset_incr;
    fv_r_beats_per_wide_next = fv_r_beats_per_wide;
    fv_r_beats_remaining_next = fv_r_beats_remaining;
    fv_wide_rdata_cur = fv_wide_rdata_saved[fv_rid_idx];
    fv_wide_rdata_saved_next = fv_wide_rdata_saved;
    fv_wide_rresp_rank_cur = fv_wide_rresp_rank_saved[fv_rid_idx];
    fv_wide_rresp_rank_saved_next = fv_wide_rresp_rank_saved;

    if (fv_wide_ar_hs) begin
      // A new accepted AR seeds the slot's reconstruction parameters and
      // clears any partial wide beat state for that internal request slot.
      fv_r_is_fixed_next[wide_arid[InternalIdWidth-1:0]] = wide_arburst == br_amba::AxiBurstFixed;
      fv_r_offset_next[wide_arid[InternalIdWidth-1:0]] = fv_wide_ar_offset;
      fv_r_offset_incr_next[wide_arid[InternalIdWidth-1:0]] = fv_r_offset_incr_cfg;
      fv_r_beats_per_wide_next[wide_arid[InternalIdWidth-1:0]] = fv_r_beats_per_wide_cfg;
      fv_r_beats_remaining_next[wide_arid[InternalIdWidth-1:0]] = fv_r_beats_per_wide_cfg;
      fv_wide_rdata_saved_next[wide_arid[InternalIdWidth-1:0]] = '0;
      fv_wide_rresp_rank_saved_next[wide_arid[InternalIdWidth-1:0]] = '0;
    end

    if (fv_narrow_r_hs) begin
      // Merge the current narrow beat into the slot's partial wide beat and
      // update the saved response severity if this beat is worse.
      fv_wide_rdata_cur[fv_r_lane_cur*NarrowDataWidth+:NarrowDataWidth] = narrow_rdata;
      fv_wide_rresp_rank_cur = fv_r_resp_rank_next;
      fv_r_offset_next[fv_rid_idx] = fv_r_offset_after_beat;

      if (fv_r_beat_done) begin
        // This beat completes the reconstructed wide beat, so reset the
        // partial data and reload the beat counter for the next wide beat.
        fv_r_beats_remaining_next[fv_rid_idx] = fv_r_beats_per_wide[fv_rid_idx];
        fv_wide_rdata_saved_next[fv_rid_idx] = '0;
        fv_wide_rresp_rank_saved_next[fv_rid_idx] = '0;
      end else begin
        // Otherwise keep accumulating until the remaining-beat counter reaches 1.
        fv_r_beats_remaining_next[fv_rid_idx] =
            fv_r_beats_remaining[fv_rid_idx] - BeatsPerWideWidth'(1);
        fv_wide_rdata_saved_next[fv_rid_idx] = fv_wide_rdata_cur;
        fv_wide_rresp_rank_saved_next[fv_rid_idx] = fv_wide_rresp_rank_cur;
      end
    end
  end

  `BR_REGL(fv_r_is_fixed, fv_r_is_fixed_next, fv_wide_ar_hs)
  `BR_REGL(fv_r_offset, fv_r_offset_next, fv_wide_ar_hs || fv_narrow_r_hs)
  `BR_REGL(fv_r_offset_incr, fv_r_offset_incr_next, fv_wide_ar_hs)
  `BR_REGL(fv_r_beats_per_wide, fv_r_beats_per_wide_next, fv_wide_ar_hs)
  `BR_REGL(fv_r_beats_remaining, fv_r_beats_remaining_next, fv_wide_ar_hs || fv_narrow_r_hs)
  `BR_REGL(fv_wide_rdata_saved, fv_wide_rdata_saved_next, fv_wide_ar_hs || fv_narrow_r_hs)
  `BR_REGL(fv_wide_rresp_rank_saved, fv_wide_rresp_rank_saved_next, fv_wide_ar_hs || fv_narrow_r_hs)

  assign fv_wide_rresp_cur = fv_rank_resp(fv_wide_rresp_rank_cur);

  assign fv_wide_r_payload = {
    narrow_rid, fv_wide_rdata_cur, narrow_ruser, fv_wide_rresp_cur, narrow_rlast
  };

  // Checks that the reconstructed wide R payload from the narrow interface
  // matches the RTL wide R channel.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(RPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxOutstandingReqs)
  ) r_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_wide_rdata_vld),
      .incoming_data(fv_wide_r_payload),
      .outgoing_vld(wide_rvalid && wide_rready),
      .outgoing_data({wide_rid, wide_rdata, wide_ruser, wide_rresp, wide_rlast})
  );

  // ----------AW channel----------
  always_comb begin
    aw_shift = 0;
    fv_narrow_awsize = wide_awsize;

    if (wide_awsize > NarrowSizeLog2) begin
      fv_narrow_awsize = NarrowSizeLog2;
      aw_shift = wide_awsize - NarrowSizeLog2;
    end

    // AXI len encodes beats - 1, so after scaling the beat count by the width ratio
    // we subtract 1 to convert back to the AXI burst-length encoding.
    fv_narrow_awlen_ext = (({1'b0, wide_awlen} + 1'b1) << aw_shift) - 1'b1;
    fv_narrow_awlen = fv_narrow_awlen_ext[br_amba::AxiBurstLenWidth-1:0];
  end

  assign fv_narrow_aw_payload = {
    wide_awaddr,
    wide_awid,
    fv_narrow_awlen,
    fv_narrow_awsize,
    wide_awburst,
    wide_awprot,
    wide_awuser
  };

  // Checks that the RTL narrow AW channel matches the monitor prediction for
  // narrow awlen/awsize derived from each accepted wide AW request.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AwPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(WriteMaxPending)
  ) aw_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(wide_awvalid && wide_awready),
      .incoming_data(fv_narrow_aw_payload),
      .outgoing_vld(narrow_awvalid && narrow_awready),
      .outgoing_data({
        narrow_awaddr,
        narrow_awid,
        narrow_awlen,
        narrow_awsize,
        narrow_awburst,
        narrow_awprot,
        narrow_awuser
      })
  );

  // ----------B channel----------
  // Checks that the wide B channel matches the narrow B channel response payload.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(BPayloadWidth),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(WriteMaxPending)
  ) b_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(narrow_bvalid && narrow_bready),
      .incoming_data({narrow_bid, narrow_buser, narrow_bresp}),
      .outgoing_vld(wide_bvalid && wide_bready),
      .outgoing_data({wide_bid, wide_buser, wide_bresp})
  );

  // ----------W channel----------
  // Queue accepted AW-derived write contexts in a FIFO. The head context stays
  // active across wide-W beats until its final wide_wlast handshake.
  assign fv_narrow_w_hs = narrow_wvalid && narrow_wready;
  assign fv_wide_w_hs = wide_wvalid && wide_wready;
  assign fv_w_fifo_push = wide_awvalid && wide_awready;
  assign fv_w_offset_incr_cfg = BeatOffsetIncrWidth'(1'b1) << fv_narrow_awsize;
  assign fv_w_beats_per_wide_cfg = BeatsPerWideWidth'(1'b1) << aw_shift;
  assign fv_w_fifo_push_ctx = '{
          is_fixed: wide_awburst == br_amba::AxiBurstFixed,
          offset: wide_awaddr[ByteOffsetWidth-1:0],
          offset_incr: fv_w_offset_incr_cfg,
          beats_per_wide: fv_w_beats_per_wide_cfg
      };
  assign fv_w_fifo_push_data = fv_w_fifo_push_ctx;
  assign fv_w_fifo_pop_ctx = fv_w_fifo_pop_data;
  assign fv_w_active_load = !fv_w_active_valid && (!fv_w_fifo_empty || fv_w_fifo_push);
  assign fv_w_ctx_valid = fv_w_active_valid || fv_w_active_load;
  assign fv_w_ctx = fv_w_active_valid ? fv_w_active_ctx : fv_w_fifo_pop_ctx;
  assign fv_w_offset_after_wide_beat = fv_w_ctx.is_fixed ? fv_w_ctx.offset :
      ByteOffsetWidth'(fv_w_ctx.offset + (fv_w_ctx.beats_per_wide * fv_w_ctx.offset_incr));
  assign fv_w_beat_start = fv_wide_w_hs;
  assign fv_w_active_done = fv_wide_w_hs && wide_wlast;

  fv_fifo #(
      .Depth(WriteMaxPending),
      .DataWidth(WFifoPayloadWidth),
      .Bypass(1)
  ) w_fifo (
      .clk(clk),
      .rst(rst),
      .push(fv_w_fifo_push),
      .push_data(fv_w_fifo_push_data),
      .pop(fv_w_active_load),
      .pop_data(fv_w_fifo_pop_data),
      .empty(fv_w_fifo_empty),
      .full()
  );

  always_comb begin
    logic [ByteOffsetWidth-1:0] chunk_offset;
    logic [LaneIdxWidth-1:0] chunk_lane;

    fv_narrow_w_pred_vld = '0;
    fv_narrow_w_pred_payloads = '0;
    chunk_offset = '0;
    chunk_lane = '0;

    if (fv_w_ctx_valid) begin
      chunk_offset = fv_w_ctx.offset;

      for (int i = 0; i < LanesPerWide; i++) begin
        // Multi-input scoreboard mode lets one wide W beat enqueue every
        // narrow beat it will serialize into. Keep the chunks in serializer
        // order, not lane order:
        // 2:1 example: chunk 0 is the first narrow beat sent, chunk 1 is the
        // second. For aligned INCR bursts that is low lane first, then high.
        chunk_lane = LaneIdxWidth'(chunk_offset >> NarrowSizeLog2);

        if (fv_w_beat_start && (BeatsPerWideWidth'(i) < fv_w_ctx.beats_per_wide)) begin
          fv_narrow_w_pred_vld[i] = 1'b1;
          fv_narrow_w_pred_payloads[i] = {
            wide_wdata[chunk_lane*NarrowDataWidth+:NarrowDataWidth],
            wide_wstrb[chunk_lane*NarrowStrobeWidth+:NarrowStrobeWidth],
            wide_wuser,
            wide_wlast && (BeatsPerWideWidth'(i + 1) == fv_w_ctx.beats_per_wide)
          };
        end

        if ((i + 1) < LanesPerWide) begin
          if (!fv_w_ctx.is_fixed) begin
            chunk_offset = chunk_offset + fv_w_ctx.offset_incr;
          end
        end
      end
    end
  end

  always_comb begin
    fv_w_active_offset_next = fv_w_active_ctx.offset;

    if (fv_w_active_load) begin
      fv_w_active_offset_next = fv_w_fifo_pop_ctx.offset;
    end

    if (fv_wide_w_hs && !fv_w_active_done) begin
      fv_w_active_offset_next = fv_w_offset_after_wide_beat;
    end
  end

  `BR_REG(fv_w_active_valid, fv_w_ctx_valid && !fv_w_active_done)
  `BR_REGL(fv_w_active_ctx.is_fixed, fv_w_fifo_pop_ctx.is_fixed, fv_w_active_load)
  `BR_REGL(fv_w_active_ctx.offset, fv_w_active_offset_next, fv_w_active_load || fv_wide_w_hs)
  `BR_REGL(fv_w_active_ctx.offset_incr, fv_w_fifo_pop_ctx.offset_incr, fv_w_active_load)
  `BR_REGL(fv_w_active_ctx.beats_per_wide, fv_w_fifo_pop_ctx.beats_per_wide, fv_w_active_load)

  // Enqueue every narrow beat for one wide W beat at serializer start. The
  // scoreboard then drains them one per actual narrow-W handshake, absorbing
  // any latency added by RegisterNarrowOutputs.
  // Example, 2:1 shrink:
  // one wide W beat enqueues two predicted narrow chunks on fv_w_beat_start.
  // chunk 0 is the first serialized narrow beat; chunk 1 is the second.
  // For aligned INCR traffic that is lower lane first, then higher lane.
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(WPayloadWidth),
      .IN_CHUNKS(LanesPerWide),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(WriteMaxPending)
  ) w_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_narrow_w_pred_vld),
      .incoming_data(fv_narrow_w_pred_payloads),
      .outgoing_vld(narrow_wvalid && narrow_wready),
      .outgoing_data({narrow_wdata, narrow_wstrb, narrow_wuser, narrow_wlast})
  );

  // ----------AXI protocols----------
  axi4_master #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(WideDataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      // When there is no valid, ready does not need to rise eventually.
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1),
      // stable assumptions will be applied to data and mask, instead of mased_data (data & mask)
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0),
      // Confirmed with Howard, RTL doesn't restrict write at all.
      // If no b_valid is returned after MaxPending writes, aw_ready won't de-assert.
      .CDNS_READY_OVFLOW_CHECKS(0),
      // To disable Dbc (Data before Control) checks
      // for wide side, aw is always before w
      .DATA_ACCEPT_WITH_OR_AFTER_CONTROL(1)
  ) wide (
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      .awvalid (wide_awvalid),
      .awready (wide_awready),
      .awid    (wide_awid),
      .awaddr  (wide_awaddr),
      .awlen   (wide_awlen),
      .awsize  (wide_awsize),
      .awburst (wide_awburst),
      .awuser  (wide_awuser),
      .awprot  (wide_awprot),
      .awlock  (),
      .awcache (),
      .awqos   (),
      .awregion(),
      .wvalid  (wide_wvalid),
      .wready  (wide_wready),
      .wdata   (wide_wdata),
      .wstrb   (wide_wstrb),
      .wlast   (wide_wlast),
      .wuser   (wide_wuser),
      .bvalid  (wide_bvalid),
      .bready  (wide_bready),
      .bid     (wide_bid),
      .bresp   (wide_bresp),
      .buser   (wide_buser),
      .arvalid (wide_arvalid),
      .arready (wide_arready),
      .arid    (wide_arid),
      .araddr  (wide_araddr),
      .arlen   (wide_arlen),
      .arsize  (wide_arsize),
      .arburst (wide_arburst),
      .aruser  (wide_aruser),
      .arprot  (wide_arprot),
      .arlock  (),
      .arcache (),
      .arqos   (),
      .arregion(),
      .rvalid  (wide_rvalid),
      .rready  (wide_rready),
      .ruser   (wide_ruser),
      .rid     (wide_rid),
      .rdata   (wide_rdata),
      .rresp   (wide_rresp),
      .rlast   (wide_rlast)
  );

  axi4_slave #(
      .ADDR_WIDTH(AddrWidth),
      .DATA_WIDTH(NarrowDataWidth),
      .ID_WIDTH(IdWidth),
      .AWUSER_WIDTH(AWUserWidth),
      .ARUSER_WIDTH(ARUserWidth),
      .WUSER_WIDTH(WUserWidth),
      .BUSER_WIDTH(BUserWidth),
      .RUSER_WIDTH(RUserWidth),
      .MAX_PENDING(MaxPending),
      .MAX_PENDING_WR(MaxPending),
      .MAX_PENDING_RD(MaxOutstandingReqs),
      // When there is no valid, ready does not need to rise eventually.
      .CONFIG_WAIT_FOR_VALID_BEFORE_READY(1),
      .ALLOW_SPARSE_STROBE(1),
      .BYTE_STROBE_ON(1),
      // stable assertions will be applied to data and mask, instead of mased_data (data & mask)
      .CONFIG_WDATA_MASKED(0),
      .CONFIG_RDATA_MASKED(0),
      // To disable Dbc (Data before Control) checks
      // some assertions' precondition is unreachable
      .DATA_BEFORE_CONTROL_ON(0)
  ) narrow (
      .aclk    (clk),
      .aresetn (!rst),
      .csysreq (1'b1),
      .csysack (1'b1),
      .cactive (1'b1),
      .awvalid (narrow_awvalid),
      .awready (narrow_awready),
      .awid    (narrow_awid),
      .awaddr  (narrow_awaddr),
      .awlen   (narrow_awlen),
      .awsize  (narrow_awsize),
      .awburst (narrow_awburst),
      .awuser  (narrow_awuser),
      .awprot  (narrow_awprot),
      .awlock  ('d0),
      .awcache ('d0),
      .awqos   ('d0),
      .awregion('d0),
      .wvalid  (narrow_wvalid),
      .wready  (narrow_wready),
      .wdata   (narrow_wdata),
      .wstrb   (narrow_wstrb),
      .wlast   (narrow_wlast),
      .wuser   (narrow_wuser),
      .bvalid  (narrow_bvalid),
      .bready  (narrow_bready),
      .bid     (narrow_bid),
      .bresp   (narrow_bresp),
      .buser   (narrow_buser),
      .arvalid (narrow_arvalid),
      .arready (narrow_arready),
      .arid    (narrow_arid),
      .araddr  (narrow_araddr),
      .arlen   (narrow_arlen),
      .arsize  (narrow_arsize),
      .arburst (narrow_arburst),
      .aruser  (narrow_aruser),
      .arprot  (narrow_arprot),
      .arlock  ('d0),
      .arcache ('d0),
      .arqos   ('d0),
      .arregion('d0),
      .rvalid  (narrow_rvalid),
      .rready  (narrow_rready),
      .ruser   (narrow_ruser),
      .rid     (narrow_rid),
      .rdata   (narrow_rdata),
      .rresp   (narrow_rresp),
      .rlast   (narrow_rlast)
  );

endmodule : br_amba_axi_shrinker_fpv_monitor

bind br_amba_axi_shrinker br_amba_axi_shrinker_fpv_monitor #(
    .AddrWidth(AddrWidth),
    .WideDataWidth(WideDataWidth),
    .NarrowDataWidth(NarrowDataWidth),
    .IdWidth(IdWidth),
    .AWUserWidth(AWUserWidth),
    .ARUserWidth(ARUserWidth),
    .WUserWidth(WUserWidth),
    .BUserWidth(BUserWidth),
    .RUserWidth(RUserWidth),
    .MaxOutstandingReqs(MaxOutstandingReqs),
    .WriteFifoDepth(WriteFifoDepth),
    .RegisterNarrowOutputs(RegisterNarrowOutputs),
    .RegisterWideOutputs(RegisterWideOutputs)
) monitor (.*);
