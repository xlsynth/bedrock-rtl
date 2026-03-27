// SPDX-License-Identifier: Apache-2.0

// AXI Shrinker
//
// This module takes an AXI4 interface of a given width and shrinks it
// to a narrower width. The rules for converting transactions are as follows:
//
// - Transactions with size larger than the target width
//   - Size is converted to the maximum size for the target width
//   - Length is multiplied by request_size / target_size
//   - For write transactions, the data and strobe are serialized
//     starting from the lower bits.
//   - For read transactions, the responses are coalesced so that
//     the number of responses matches the length of the original request.
// - Transactions with size less than or equal to the target width
//   - Request is passed through unchanged.
//   - For write transactions, a word lane is selected from the
//     original wdata and wstrb so that the correct one is used on the target side.
//   - For read transactions, the rdata is shifted to the correct position in the wide rdata.
//
// Shrinking is only supported for transactions with burst type BURST_INCR.
// Transactions with other burst types must have size less than or equal to the narrow width.

`include "br_asserts_internal.svh"
`include "br_assign.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_axi_shrinker #(
    parameter int AddrWidth = 12,  // Must be at least 12
    parameter int WideDataWidth = 16,  // Must be at least 16
    parameter int NarrowDataWidth = 8,  // Must be at least 8
    parameter int IdWidth = 1,  // Must be at least 1
    parameter int AWUserWidth = 1,  // Must be at least 1
    parameter int ARUserWidth = 1,  // Must be at least 1
    parameter int WUserWidth = 1,  // Must be at least 1
    parameter int BUserWidth = 1,  // Must be at least 1
    parameter int RUserWidth = 1,  // Must be at least 1
    // Must be at least 1 and <= (2 ** IdWidth).
    // Must be a power of two.
    // This parameter controls how many read requests can be inflight before
    // the wide ar interface is backpressured. A table of this size is constructed
    // to track each inflight read request. The lower $clog2(MaxOutstandingReqs)
    // bits of the ID is used to determine the table index, so any collision in these
    // bits will result in the second request being blocked from issuing on the narrow interface.
    parameter int MaxOutstandingReqs = 1,
    // Depth of the FIFO used to keep information from the AW channel while
    // the write data is being serialized to the narrow interface.
    // This should be sized to be equal to the average lag between the arrival
    // of the write address and first beat of the write data.
    parameter int WriteFifoDepth = 1,
    // If 1, the narrow AW, W, and AR outputs are registered directly, improving
    // timing at the cost of an additional cycle of latency.
    parameter bit RegisterNarrowOutputs = 1,
    // If 1, the wide B and R outputs are registered directly, improving
    // timing at the cost of an additional cycle of latency.
    parameter bit RegisterWideOutputs = 1,
    localparam int WideStrobeWidth = WideDataWidth / 8,
    localparam int NarrowStrobeWidth = NarrowDataWidth / 8
) (
    input logic clk,
    input logic rst,

    // Wide AXI4 interface
    input  logic [                 AddrWidth-1:0] wide_awaddr,
    input  logic [                   IdWidth-1:0] wide_awid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] wide_awlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] wide_awsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] wide_awburst,
    input  logic [     br_amba::AxiProtWidth-1:0] wide_awprot,
    input  logic [               AWUserWidth-1:0] wide_awuser,
    input  logic                                  wide_awvalid,
    output logic                                  wide_awready,
    input  logic [             WideDataWidth-1:0] wide_wdata,
    input  logic [           WideStrobeWidth-1:0] wide_wstrb,
    input  logic [                WUserWidth-1:0] wide_wuser,
    input  logic                                  wide_wlast,
    input  logic                                  wide_wvalid,
    output logic                                  wide_wready,
    output logic [                   IdWidth-1:0] wide_bid,
    output logic [                BUserWidth-1:0] wide_buser,
    output logic [     br_amba::AxiRespWidth-1:0] wide_bresp,
    output logic                                  wide_bvalid,
    input  logic                                  wide_bready,
    input  logic [                 AddrWidth-1:0] wide_araddr,
    input  logic [                   IdWidth-1:0] wide_arid,
    input  logic [ br_amba::AxiBurstLenWidth-1:0] wide_arlen,
    input  logic [br_amba::AxiBurstSizeWidth-1:0] wide_arsize,
    input  logic [br_amba::AxiBurstTypeWidth-1:0] wide_arburst,
    input  logic [     br_amba::AxiProtWidth-1:0] wide_arprot,
    input  logic [               ARUserWidth-1:0] wide_aruser,
    input  logic                                  wide_arvalid,
    output logic                                  wide_arready,
    output logic [                   IdWidth-1:0] wide_rid,
    output logic [             WideDataWidth-1:0] wide_rdata,
    output logic [                RUserWidth-1:0] wide_ruser,
    output logic [     br_amba::AxiRespWidth-1:0] wide_rresp,
    output logic                                  wide_rlast,
    output logic                                  wide_rvalid,
    input  logic                                  wide_rready,

    output logic [                 AddrWidth-1:0] narrow_awaddr,
    output logic [                   IdWidth-1:0] narrow_awid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] narrow_awlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] narrow_awsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] narrow_awburst,
    output logic [     br_amba::AxiProtWidth-1:0] narrow_awprot,
    output logic [               AWUserWidth-1:0] narrow_awuser,
    output logic                                  narrow_awvalid,
    input  logic                                  narrow_awready,
    output logic [           NarrowDataWidth-1:0] narrow_wdata,
    output logic [         NarrowStrobeWidth-1:0] narrow_wstrb,
    output logic [                WUserWidth-1:0] narrow_wuser,
    output logic                                  narrow_wlast,
    output logic                                  narrow_wvalid,
    input  logic                                  narrow_wready,
    input  logic [                   IdWidth-1:0] narrow_bid,
    input  logic [                BUserWidth-1:0] narrow_buser,
    input  logic [     br_amba::AxiRespWidth-1:0] narrow_bresp,
    input  logic                                  narrow_bvalid,
    output logic                                  narrow_bready,
    output logic [                 AddrWidth-1:0] narrow_araddr,
    output logic [                   IdWidth-1:0] narrow_arid,
    output logic [ br_amba::AxiBurstLenWidth-1:0] narrow_arlen,
    output logic [br_amba::AxiBurstSizeWidth-1:0] narrow_arsize,
    output logic [br_amba::AxiBurstTypeWidth-1:0] narrow_arburst,
    output logic [     br_amba::AxiProtWidth-1:0] narrow_arprot,
    output logic [               ARUserWidth-1:0] narrow_aruser,
    output logic                                  narrow_arvalid,
    input  logic                                  narrow_arready,
    input  logic [                   IdWidth-1:0] narrow_rid,
    input  logic [           NarrowDataWidth-1:0] narrow_rdata,
    input  logic [                RUserWidth-1:0] narrow_ruser,
    input  logic [     br_amba::AxiRespWidth-1:0] narrow_rresp,
    input  logic                                  narrow_rlast,
    input  logic                                  narrow_rvalid,
    output logic                                  narrow_rready
);

  // Local Parameters

  localparam int WideSizeLog2 = $clog2(WideStrobeWidth);
  localparam int NarrowSizeLog2 = $clog2(NarrowStrobeWidth);
  localparam int LanesPerWide = WideDataWidth / NarrowDataWidth;
  localparam int LaneSelWidth = br_math::clamped_clog2(LanesPerWide);
  localparam int ByteOffsetWidth = br_math::clamped_clog2(WideStrobeWidth);

  // Integration Assertions

  `BR_ASSERT_STATIC(addr_width_must_be_at_least_12_a, AddrWidth >= 12)
  `BR_ASSERT_STATIC(wide_data_width_must_be_at_least_16_a, WideDataWidth >= 16)
  `BR_ASSERT_STATIC(narrow_data_width_must_be_at_least_8_a, NarrowDataWidth >= 8)
  `BR_ASSERT_STATIC(id_width_must_be_at_least_1_a, IdWidth >= 1)
  `BR_ASSERT_STATIC(awuser_width_must_be_at_least_1_a, AWUserWidth >= 1)
  `BR_ASSERT_STATIC(aruser_width_must_be_at_least_1_a, ARUserWidth >= 1)
  `BR_ASSERT_STATIC(wuser_width_must_be_at_least_1_a, WUserWidth >= 1)
  `BR_ASSERT_STATIC(buser_width_must_be_at_least_1_a, BUserWidth >= 1)
  `BR_ASSERT_STATIC(ruser_width_must_be_at_least_1_a, RUserWidth >= 1)
  `BR_ASSERT_STATIC(max_outstanding_reqs_in_range_a,
                    MaxOutstandingReqs >= 1 && MaxOutstandingReqs <= (2 ** IdWidth))
  `BR_ASSERT_STATIC(max_outstanding_reqs_must_be_pow2_a, br_math::is_power_of_2(MaxOutstandingReqs))
  `BR_ASSERT_STATIC(wide_data_width_must_be_pow2_a, br_math::is_power_of_2(WideDataWidth))
  `BR_ASSERT_STATIC(narrow_data_width_must_be_pow2_a, br_math::is_power_of_2(NarrowDataWidth))
  `BR_ASSERT_STATIC(wide_data_width_must_be_greater_than_narrow_a, WideDataWidth > NarrowDataWidth)

  `BR_ASSERT_INTG(wide_awsize_okay_a, wide_awvalid |-> wide_awsize <= WideSizeLog2)
  `BR_ASSERT_INTG(wide_arsize_okay_a, wide_arvalid |-> wide_arsize <= WideSizeLog2)
  `BR_ASSERT_INTG(
      shrinking_awburst_incr_a,
      (wide_awvalid && wide_awsize > NarrowSizeLog2) |-> wide_awburst == br_amba::AxiBurstIncr)
  `BR_ASSERT_INTG(
      shrinking_arburst_incr_a,
      (wide_arvalid && wide_arsize > NarrowSizeLog2) |-> wide_arburst == br_amba::AxiBurstIncr)

`ifndef BR_DISABLE_INTG_CHECKS
`ifdef BR_ASSERT_ON
  localparam int ExtBurstLenWidth = br_amba::AxiBurstLenWidth + WideSizeLog2 - NarrowSizeLog2;
  localparam int MaxBurstLen = 2 ** br_amba::AxiBurstLenWidth - 1;

  logic [ExtBurstLenWidth-1:0] ext_wide_awlen;
  logic [ExtBurstLenWidth-1:0] ext_wide_arlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_awlen;
  logic [ExtBurstLenWidth-1:0] ext_narrow_arlen;

  assign ext_wide_awlen = ExtBurstLenWidth'(wide_awlen);
  assign ext_wide_arlen = ExtBurstLenWidth'(wide_arlen);

  // ri lint_check_off TRUNC_LSHIFT VAR_SHIFT
  assign ext_narrow_awlen =
      (wide_awsize > NarrowSizeLog2) ?
      ((ext_wide_awlen + 1'b1) << (wide_awsize - NarrowSizeLog2)) - 1'b1 : ext_wide_awlen;
  assign ext_narrow_arlen =
      (wide_arsize > NarrowSizeLog2) ?
      ((ext_wide_arlen + 1'b1) << (wide_arsize - NarrowSizeLog2)) - 1'b1 : ext_wide_arlen;
  // ri lint_check_on TRUNC_LSHIFT VAR_SHIFT

  `BR_ASSERT_INTG(narrow_awlen_no_overflow_a, wide_awvalid |-> ext_narrow_awlen <= MaxBurstLen)
  `BR_ASSERT_INTG(narrow_arlen_no_overflow_a, wide_arvalid |-> ext_narrow_arlen <= MaxBurstLen)
`endif
`endif

  // Implementation

  logic [                 AddrWidth-1:0] narrow_awaddr_int;
  logic [                   IdWidth-1:0] narrow_awid_int;
  logic [ br_amba::AxiBurstLenWidth-1:0] narrow_awlen_int;
  logic [br_amba::AxiBurstSizeWidth-1:0] narrow_awsize_int;
  logic [br_amba::AxiBurstTypeWidth-1:0] narrow_awburst_int;
  logic [     br_amba::AxiProtWidth-1:0] narrow_awprot_int;
  logic [               AWUserWidth-1:0] narrow_awuser_int;
  logic                                  narrow_awvalid_int;
  logic                                  narrow_awready_int;

  logic [           NarrowDataWidth-1:0] narrow_wdata_int;
  logic [         NarrowStrobeWidth-1:0] narrow_wstrb_int;
  logic [                WUserWidth-1:0] narrow_wuser_int;
  logic                                  narrow_wlast_int;
  logic                                  narrow_wvalid_int;
  logic                                  narrow_wready_int;

  logic [                 AddrWidth-1:0] narrow_araddr_int;
  logic [                   IdWidth-1:0] narrow_arid_int;
  logic [ br_amba::AxiBurstLenWidth-1:0] narrow_arlen_int;
  logic [br_amba::AxiBurstSizeWidth-1:0] narrow_arsize_int;
  logic [br_amba::AxiBurstTypeWidth-1:0] narrow_arburst_int;
  logic [     br_amba::AxiProtWidth-1:0] narrow_arprot_int;
  logic [               ARUserWidth-1:0] narrow_aruser_int;
  logic                                  narrow_arvalid_int;
  logic                                  narrow_arready_int;

  logic                                  wide_bvalid_int;
  logic                                  wide_bready_int;
  logic [     br_amba::AxiRespWidth-1:0] wide_bresp_int;
  logic [                   IdWidth-1:0] wide_bid_int;
  logic [                BUserWidth-1:0] wide_buser_int;

  logic                                  wide_rvalid_int;
  logic                                  wide_rready_int;
  logic [             WideDataWidth-1:0] wide_rdata_int;
  logic [                RUserWidth-1:0] wide_ruser_int;
  logic [     br_amba::AxiRespWidth-1:0] wide_rresp_int;
  logic                                  wide_rlast_int;
  logic [                   IdWidth-1:0] wide_rid_int;

  // Read/Write Address Remapping

  // These fields are just passed through as-is
  assign narrow_awaddr_int = wide_awaddr;
  assign narrow_awid_int = wide_awid;
  assign narrow_awburst_int = wide_awburst;
  assign narrow_awprot_int = wide_awprot;
  assign narrow_awuser_int = wide_awuser;

  assign narrow_araddr_int = wide_araddr;
  assign narrow_arid_int = wide_arid;
  assign narrow_arburst_int = wide_arburst;
  assign narrow_arprot_int = wide_arprot;
  assign narrow_aruser_int = wide_aruser;

  // Size and length conversion
  localparam int MaxShift = WideSizeLog2 - NarrowSizeLog2;
  localparam int ShiftWidth = $clog2(MaxShift + 1);

  logic aw_large_size;
  logic ar_large_size;
  logic [br_amba::AxiBurstSizeWidth-1:0] awsize_diff_ext;
  logic [br_amba::AxiBurstSizeWidth-1:0] arsize_diff_ext;
  logic [ShiftWidth-1:0] awsize_diff;
  logic [ShiftWidth-1:0] arsize_diff;

  assign aw_large_size = (wide_awsize > NarrowSizeLog2);
  assign ar_large_size = (wide_arsize > NarrowSizeLog2);

  // Size just clamps at the maximum narrow size
  assign narrow_awsize_int = aw_large_size ? NarrowSizeLog2 : wide_awsize;
  assign narrow_arsize_int = ar_large_size ? NarrowSizeLog2 : wide_arsize;

  assign awsize_diff_ext = aw_large_size ? (wide_awsize - NarrowSizeLog2) : '0;
  assign arsize_diff_ext = ar_large_size ? (wide_arsize - NarrowSizeLog2) : '0;

  assign awsize_diff = awsize_diff_ext[ShiftWidth-1:0];
  assign arsize_diff = arsize_diff_ext[ShiftWidth-1:0];

  // If the size is too large, the final length should be
  // wide_length * (wide_size / max_narrow_size)
  // This is equivalent to left shifting by the difference in the log2 domain.
  // However, since awlen/arlen is actually length - 1, we need to fill the LSBs
  // with 1s instead of 0s.
  br_shift_left #(
      .NumSymbols(br_amba::AxiBurstLenWidth),
      .SymbolWidth(1),
      .MaxShift(MaxShift)
  ) br_shift_left_awlen (
      .in(wide_awlen),
      .shift(awsize_diff),
      .fill(1'b1),
      .out_valid(),
      .out(narrow_awlen_int)
  );

  br_shift_left #(
      .NumSymbols(br_amba::AxiBurstLenWidth),
      .SymbolWidth(1),
      .MaxShift(MaxShift)
  ) br_shift_left_arlen (
      .in(wide_arlen),
      .shift(arsize_diff),
      .fill(1'b1),
      .out_valid(),
      .out(narrow_arlen_int)
  );

  if (ShiftWidth < br_amba::AxiBurstSizeWidth) begin : gen_unused_size_diff_msbs
    `BR_UNUSED_NAMED(awsize_diff_ext, awsize_diff_ext[br_amba::AxiBurstSizeWidth-1:ShiftWidth])
    `BR_UNUSED_NAMED(arsize_diff_ext, arsize_diff_ext[br_amba::AxiBurstSizeWidth-1:ShiftWidth])
  end

  // Write FIFO
  // Need to keep some information so that write data can be sent correctly
  // We need to save the original offset so that we know which of the
  // data lanes we should select the data and strobe from.
  // We need to know the size and burst so we know how much to increment
  // the offset by each time.
  // Finally, we need to know how much the size was reduced by so that we know
  // how many narrow beats each wide beat will be serialized to.
  typedef struct packed {
    logic [ByteOffsetWidth-1:0] offset;
    logic [br_amba::AxiBurstSizeWidth-1:0] size;
    br_amba::axi_burst_type_t burst;
    logic [ShiftWidth-1:0] shift;
  } tracking_info_t;

  logic write_fifo_push_valid;
  logic write_fifo_push_ready;
  tracking_info_t write_fifo_push_info;
  logic write_fifo_pop_valid;
  logic write_fifo_pop_ready;
  tracking_info_t write_fifo_pop_info;

  assign write_fifo_push_info = '{
          offset: narrow_awaddr_int[ByteOffsetWidth-1:0],
          size: narrow_awsize_int,
          burst: br_amba::axi_burst_type_t'(narrow_awburst_int),
          shift: awsize_diff
      };

  // Fork the wide awvalid/awready to the narrow interface and the write FIFO
  br_flow_fork #(
      .NumFlows(2)
  ) br_flow_fork_aw (
      .clk,
      .rst,
      .push_ready(wide_awready),
      .push_valid(wide_awvalid),
      .pop_valid_unstable({write_fifo_push_valid, narrow_awvalid_int}),
      .pop_ready({write_fifo_push_ready, narrow_awready_int})
  );

  if (WriteFifoDepth > 1) begin : gen_write_fifo_depth_gt1
    br_fifo_flops #(
        .Depth(WriteFifoDepth),
        .Width($bits(tracking_info_t))
    ) br_fifo_flops_write_fifo (
        .clk,
        .rst,
        .push_ready(write_fifo_push_ready),
        .push_valid(write_fifo_push_valid),
        .push_data({write_fifo_push_info}),
        .slots(),
        .slots_next(),
        .full(),
        .full_next(),
        .pop_ready(write_fifo_pop_ready),
        .pop_valid(write_fifo_pop_valid),
        .pop_data({write_fifo_pop_info}),
        .empty(),
        .empty_next(),
        .items(),
        .items_next()
    );
  end else begin : gen_write_fifo_depth_eq1
    // Use br_flow_reg_none to ensure 0 cut-through latency
    br_flow_reg_none #(
        .Width($bits(tracking_info_t))
    ) br_flow_reg_none_write_fifo (
        .clk,
        .rst,
        .push_ready(write_fifo_push_ready),
        .push_valid(write_fifo_push_valid),
        .push_data (write_fifo_push_info),
        .pop_ready (write_fifo_pop_ready),
        .pop_valid (write_fifo_pop_valid),
        .pop_data  (write_fifo_pop_info)
    );
  end

  // Write Data Remapping

  logic write_fifo_pop_beat;
  logic narrow_w_int_beat;
  logic w_sending, w_sending_next;

  logic [LaneSelWidth-1:0] w_data_sel;
  logic w_beat_last;

  assign write_fifo_pop_beat = write_fifo_pop_valid && write_fifo_pop_ready;
  assign narrow_w_int_beat = narrow_wvalid_int && narrow_wready_int;
  // Pop the FIFO if we're not sending writes or sending the last beat
  assign write_fifo_pop_ready =
    !w_sending ||
    (wide_wvalid && narrow_wready_int && narrow_wlast_int);
  assign w_sending_next =
    (w_sending && !(narrow_w_int_beat && narrow_wlast_int)) ||
    write_fifo_pop_beat;

  `BR_REG(w_sending, w_sending_next)

  // Tracker to hold the current offset and beat ID
  // We initialize when the write FIFO is popped and update each narrow write beat sent.
  br_amba_axi_resizer_beat_tracker #(
      .WideBytes  (WideStrobeWidth),
      .NarrowBytes(NarrowStrobeWidth)
  ) br_amba_axi_resizer_beat_tracker_w (
      .clk,
      .rst,

      .start_valid(write_fifo_pop_beat),
      .start_offset(write_fifo_pop_info.offset),
      .size(write_fifo_pop_info.size),
      .burst(write_fifo_pop_info.burst),
      .shift(write_fifo_pop_info.shift),

      .beat_valid(narrow_w_int_beat),
      .beat_lane (w_data_sel),
      .beat_last (w_beat_last)
  );

  assign narrow_wvalid_int = w_sending && wide_wvalid;
  assign narrow_wlast_int  = wide_wlast && w_beat_last;
  assign narrow_wuser_int  = wide_wuser;

  br_mux_bin #(
      .NumSymbolsIn(LanesPerWide),
      .SymbolWidth (NarrowDataWidth)
  ) br_mux_bin_w_data (
      .select(w_data_sel),
      .in(wide_wdata),
      .out(narrow_wdata_int),
      .out_valid()
  );

  br_mux_bin #(
      .NumSymbolsIn(LanesPerWide),
      .SymbolWidth (NarrowStrobeWidth)
  ) br_mux_bin_w_strb (
      .select(w_data_sel),
      .in(wide_wstrb),
      .out(narrow_wstrb_int),
      .out_valid()
  );

  assign wide_wready = w_sending && narrow_wready_int && w_beat_last;

  // Write response
  // Wide write response is the same as the narrow write response
  assign wide_bvalid_int = narrow_bvalid;
  assign narrow_bready = wide_bready_int;
  assign wide_bid_int = narrow_bid;
  assign wide_bresp_int = narrow_bresp;
  assign wide_buser_int = narrow_buser;

  // Read data remapping
  logic narrow_rvalid_int;
  logic narrow_rready_int;
  logic [IdWidth-1:0] narrow_rid_int;
  logic [br_amba::AxiRespWidth-1:0] narrow_rresp_int;
  logic [NarrowDataWidth-1:0] narrow_rdata_int;
  logic [RUserWidth-1:0] narrow_ruser_int;
  logic narrow_rlast_int;
  logic narrow_r_int_beat;

  // Ideally, we would allow up to MaxOutstandingReqs read requests with arbitrary IDs to
  // be sent. However, this would be quite expensive to implement since we would need to track
  // ordering for the requests with the same ID. Instead, we use the lower $clog2(MaxOutstandingReqs)
  // bits of the ID as a table index and block requests that conflict with an already used entry in the table.
  localparam int InternalIdWidth = br_math::clamped_clog2(MaxOutstandingReqs);

  logic [MaxOutstandingReqs-1:0] read_active, read_active_next;
  logic [MaxOutstandingReqs-1:0] read_active_set, read_active_clear;
  logic [InternalIdWidth-1:0] read_index;
  logic [MaxOutstandingReqs-1:0] read_index_onehot;
  logic [InternalIdWidth-1:0] resp_index;
  logic [MaxOutstandingReqs-1:0] resp_index_onehot;
  logic read_index_available;
  logic ar_beat;
  logic r_last_beat;

  assign read_index = wide_arid[InternalIdWidth-1:0];
  assign resp_index = narrow_rid[InternalIdWidth-1:0];

  br_enc_bin2onehot #(
      .NumValues(MaxOutstandingReqs)
  ) br_enc_bin2onehot_read_index (
      .clk,
      .rst,
      .in_valid(wide_arvalid),
      .in(read_index),
      .out(read_index_onehot)
  );

  br_enc_bin2onehot #(
      .NumValues(MaxOutstandingReqs)
  ) br_enc_bin2onehot_resp_index (
      .clk,
      .rst,
      .in_valid(narrow_rvalid),
      .in(resp_index),
      .out(resp_index_onehot)
  );

  assign read_index_available = !(|(read_active & read_index_onehot));
  assign ar_beat = wide_arvalid && wide_arready;
  assign r_last_beat = narrow_rvalid && narrow_rready && narrow_rlast;

  assign narrow_arvalid_int = wide_arvalid && read_index_available;
  assign wide_arready = narrow_arready_int && read_index_available;

  assign read_active_set = {MaxOutstandingReqs{ar_beat}} & read_index_onehot;
  assign read_active_clear = {MaxOutstandingReqs{r_last_beat}} & resp_index_onehot;
  assign read_active_next = (read_active | read_active_set) & ~read_active_clear;

  `BR_REG(read_active, read_active_next)

  // For read requests, we need to save all the same information that we save
  // for write requests.

  logic read_table_wr_valid;
  logic [InternalIdWidth-1:0] read_table_wr_addr;
  tracking_info_t read_table_wr_data;

  logic read_table_rd_addr_valid;
  logic [InternalIdWidth-1:0] read_table_rd_addr;
  logic read_table_rd_data_valid;
  tracking_info_t read_table_rd_data;

  assign read_table_wr_valid = ar_beat;
  assign read_table_wr_addr = read_index;
  assign read_table_wr_data = '{
          offset: narrow_araddr_int[ByteOffsetWidth-1:0],
          size: narrow_arsize_int,
          burst: br_amba::axi_burst_type_t'(narrow_arburst_int),
          shift: arsize_diff
      };

  assign read_table_rd_addr_valid = narrow_rvalid;
  assign read_table_rd_addr = resp_index;

  br_ram_flops #(
      .Depth(MaxOutstandingReqs),
      .Width($bits(tracking_info_t))
  ) br_ram_flops_read_table (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(read_table_wr_valid),
      .wr_addr(read_table_wr_addr),
      .wr_data(read_table_wr_data),
      .wr_word_en(1'b1),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(read_table_rd_addr_valid),
      .rd_addr(read_table_rd_addr),
      .rd_data_valid(read_table_rd_data_valid),
      .rd_data(read_table_rd_data)
  );

  `BR_UNUSED(read_table_rd_data_valid)

  // For each outstanding transaction, check if the current beat is the first beat of the transaction
  logic [MaxOutstandingReqs-1:0] r_first, r_first_next;
  logic narrow_r_beat;
  logic narrow_r_new;

  assign narrow_r_beat = narrow_rvalid && narrow_rready;
  assign narrow_r_new = narrow_r_beat && |(r_first & resp_index_onehot);
  assign narrow_r_int_beat = narrow_rvalid_int && narrow_rready_int;
  // Set the first bit for the index if it's the last beat
  // Clear the first bit if it's not the last beat
  assign r_first_next = narrow_rlast ? (r_first | resp_index_onehot)
                                     : (r_first & ~resp_index_onehot);

  `BR_REGLI(r_first, r_first_next, narrow_r_beat, '1)

  // Flow register to pipeline the RAM read result
  br_flow_reg_fwd #(
      .Width(IdWidth + br_amba::AxiRespWidth + RUserWidth + NarrowDataWidth + 1)
  ) br_flow_reg_fwd_narrow_r (
      .clk,
      .rst,
      .push_ready(narrow_rready),
      .push_valid(narrow_rvalid),
      .push_data({narrow_rid, narrow_rresp, narrow_ruser, narrow_rdata, narrow_rlast}),
      .pop_ready(narrow_rready_int),
      .pop_valid(narrow_rvalid_int),
      .pop_data({
        narrow_rid_int, narrow_rresp_int, narrow_ruser_int, narrow_rdata_int, narrow_rlast_int
      })
  );

  // Since R beats can be interleaved in AXI, we need tracking information for each outstanding transaction
  // and then pick the correct tracking registers to use based on the response index.
  logic [MaxOutstandingReqs-1:0] r_beat_last_per_req;
  logic [MaxOutstandingReqs-1:0][LaneSelWidth-1:0] r_data_shift_per_req;
  br_amba::axi_resp_t [MaxOutstandingReqs-1:0] wide_rresp_int_per_req;
  logic [MaxOutstandingReqs-1:0][WideDataWidth-1:0] wide_rdata_int_per_req;
  logic r_beat_last;
  logic [LaneSelWidth-1:0] r_data_shift;
  logic [WideDataWidth-1:0] wide_rdata_new;
  br_amba::axi_resp_t narrow_rresp_int_enum;
  logic [WideDataWidth-1:0] narrow_rdata_int_ext;
  logic [InternalIdWidth-1:0] r_beat_index;

  assign `BR_ZERO_EXT(narrow_rdata_int_ext, narrow_rdata_int)
  assign narrow_rresp_int_enum = br_amba::axi_resp_t'(narrow_rresp_int);
  assign r_beat_index = narrow_rid_int[InternalIdWidth-1:0];

  br_shift_left #(
      .NumSymbols(LanesPerWide),
      .SymbolWidth(NarrowDataWidth),
      .MaxShift(LanesPerWide - 1)
  ) br_shift_left_wide_rdata (
      .in(narrow_rdata_int_ext),
      .shift(r_data_shift),
      .fill('0),
      .out(wide_rdata_new),
      .out_valid()
  );

  assign wide_rvalid_int   = narrow_rvalid_int && r_beat_last;
  assign narrow_rready_int = !r_beat_last || wide_rready_int;

  typedef struct packed {
    logic [LaneSelWidth-1:0] shift;
    br_amba::axi_resp_t resp;
    logic [WideDataWidth-1:0] data;
    logic beat_last;
  } rtracker_mux_payload_t;

  rtracker_mux_payload_t [MaxOutstandingReqs-1:0] rtracker_mux_in;
  rtracker_mux_payload_t rtracker_mux_out;

  br_mux_bin #(
      .NumSymbolsIn(MaxOutstandingReqs),
      .SymbolWidth ($bits(rtracker_mux_payload_t))
  ) br_mux_bin_rtracker_mux (
      .select(r_beat_index),
      .in(rtracker_mux_in),
      .out(rtracker_mux_out),
      .out_valid()
  );

  assign r_data_shift = rtracker_mux_out.shift;
  assign r_beat_last  = rtracker_mux_out.beat_last;

  // Per transaction tracking
  // Need to keep track of the position in the beat, the offset, the accumulated data, and the coalesced response.
  for (genvar i = 0; i < MaxOutstandingReqs; i++) begin : gen_r_data_tracking
    logic tracker_start_valid;
    logic tracker_beat_valid;
    br_amba::axi_resp_t wide_rresp_saved, wide_rresp_saved_next;
    br_amba::axi_resp_t wide_rresp_comb;

    assign tracker_start_valid = narrow_r_new && resp_index_onehot[i];
    assign tracker_beat_valid  = narrow_r_int_beat && r_beat_index == i;

    br_amba_axi_resizer_beat_tracker #(
        .WideBytes  (WideStrobeWidth),
        .NarrowBytes(NarrowStrobeWidth)
    ) br_amba_axi_resizer_beat_tracker_r (
        .clk,
        .rst,

        .start_valid(tracker_start_valid),
        .start_offset(read_table_rd_data.offset),
        .size(read_table_rd_data.size),
        .burst(read_table_rd_data.burst),
        .shift(read_table_rd_data.shift),
        .beat_valid(tracker_beat_valid),
        .beat_lane(r_data_shift_per_req[i]),
        .beat_last(r_beat_last_per_req[i])
    );

    logic [WideDataWidth-1:0] wide_rdata_saved;
    logic [WideDataWidth-1:0] wide_rdata_saved_next;

    // Send the wide response based on the highest precedence response among the narrow responses
    // that compose it. The precdence is Decerr > Slverr > ExOkay > Okay.
    always_comb begin
      unique case (narrow_rresp_int_enum)
        br_amba::AxiRespOkay: wide_rresp_comb = wide_rresp_saved;
        br_amba::AxiRespExOkay:
        if (wide_rresp_saved == br_amba::AxiRespOkay) begin
          wide_rresp_comb = br_amba::AxiRespExOkay;
        end else begin
          wide_rresp_comb = wide_rresp_saved;
        end
        br_amba::AxiRespSlverr:
        if (wide_rresp_saved == br_amba::AxiRespDecerr) begin
          wide_rresp_comb = br_amba::AxiRespDecerr;
        end else begin
          wide_rresp_comb = br_amba::AxiRespSlverr;
        end
        br_amba::AxiRespDecerr: wide_rresp_comb = br_amba::AxiRespDecerr;
        default: wide_rresp_comb = br_amba::axi_resp_t'('x);
      endcase
    end
    assign wide_rresp_saved_next = r_beat_last_per_req[i] ? br_amba::AxiRespOkay : wide_rresp_comb;
    assign wide_rresp_int_per_req[i] = wide_rresp_comb;
    assign wide_rdata_int_per_req[i] = wide_rdata_new | wide_rdata_saved;
    assign wide_rdata_saved_next =
      (tracker_start_valid || r_beat_last_per_req[i]) ? '0 : wide_rdata_int_per_req[i];

    `BR_REGL(wide_rdata_saved, wide_rdata_saved_next, tracker_start_valid || tracker_beat_valid)
    `BR_REGLI(wide_rresp_saved, wide_rresp_saved_next, tracker_beat_valid, br_amba::AxiRespOkay)

    assign rtracker_mux_in[i] = '{
            shift: r_data_shift_per_req[i],
            resp: wide_rresp_int_per_req[i],
            data: wide_rdata_int_per_req[i],
            beat_last: r_beat_last_per_req[i]
        };
  end

  assign wide_rid_int   = narrow_rid_int;
  assign wide_rresp_int = {rtracker_mux_out.resp};  // flatten the enum
  assign wide_rdata_int = rtracker_mux_out.data;
  assign wide_rlast_int = narrow_rlast_int;
  assign wide_ruser_int = narrow_ruser_int;

  if (RegisterNarrowOutputs) begin : gen_narrow_reg
    br_flow_reg_fwd #(
        .Width(
          IdWidth + AddrWidth +
          br_amba::AxiBurstLenWidth + br_amba::AxiBurstSizeWidth +
          br_amba::AxiBurstTypeWidth + br_amba::AxiProtWidth +
          AWUserWidth
        )
    ) br_flow_reg_fwd_narrow_aw (
        .clk,
        .rst,
        .push_ready(narrow_awready_int),
        .push_valid(narrow_awvalid_int),
        .push_data({
          narrow_awid_int,
          narrow_awaddr_int,
          narrow_awlen_int,
          narrow_awsize_int,
          narrow_awburst_int,
          narrow_awprot_int,
          narrow_awuser_int
        }),
        .pop_ready(narrow_awready),
        .pop_valid(narrow_awvalid),
        .pop_data({
          narrow_awid,
          narrow_awaddr,
          narrow_awlen,
          narrow_awsize,
          narrow_awburst,
          narrow_awprot,
          narrow_awuser
        })
    );

    br_flow_reg_fwd #(
        .Width(
          IdWidth + AddrWidth +
          br_amba::AxiBurstLenWidth + br_amba::AxiBurstSizeWidth +
          br_amba::AxiBurstTypeWidth + br_amba::AxiProtWidth +
          ARUserWidth
        )
    ) br_flow_reg_fwd_narrow_ar (
        .clk,
        .rst,
        .push_ready(narrow_arready_int),
        .push_valid(narrow_arvalid_int),
        .push_data({
          narrow_arid_int,
          narrow_araddr_int,
          narrow_arlen_int,
          narrow_arsize_int,
          narrow_arburst_int,
          narrow_arprot_int,
          narrow_aruser_int
        }),
        .pop_ready(narrow_arready),
        .pop_valid(narrow_arvalid),
        .pop_data({
          narrow_arid,
          narrow_araddr,
          narrow_arlen,
          narrow_arsize,
          narrow_arburst,
          narrow_arprot,
          narrow_aruser
        })
    );

    br_flow_reg_fwd #(
        .Width(NarrowDataWidth + NarrowStrobeWidth + WUserWidth + 1)
    ) br_flow_reg_fwd_narrow_w (
        .clk,
        .rst,
        .push_ready(narrow_wready_int),
        .push_valid(narrow_wvalid_int),
        .push_data ({narrow_wdata_int, narrow_wstrb_int, narrow_wuser_int, narrow_wlast_int}),
        .pop_ready (narrow_wready),
        .pop_valid (narrow_wvalid),
        .pop_data  ({narrow_wdata, narrow_wstrb, narrow_wuser, narrow_wlast})
    );


  end else begin : gen_no_narrow_reg
    assign narrow_awvalid = narrow_awvalid_int;
    assign narrow_awready_int = narrow_awready;
    assign narrow_awid = narrow_awid_int;
    assign narrow_awaddr = narrow_awaddr_int;
    assign narrow_awlen = narrow_awlen_int;
    assign narrow_awsize = narrow_awsize_int;
    assign narrow_awburst = narrow_awburst_int;
    assign narrow_awprot = narrow_awprot_int;
    assign narrow_awuser = narrow_awuser_int;
    assign narrow_wvalid = narrow_wvalid_int;
    assign narrow_wready_int = narrow_wready;
    assign narrow_wdata = narrow_wdata_int;
    assign narrow_wstrb = narrow_wstrb_int;
    assign narrow_wuser = narrow_wuser_int;
    assign narrow_wlast = narrow_wlast_int;
    assign narrow_arvalid = narrow_arvalid_int;
    assign narrow_arready_int = narrow_arready;
    assign narrow_arid = narrow_arid_int;
    assign narrow_araddr = narrow_araddr_int;
    assign narrow_arlen = narrow_arlen_int;
    assign narrow_arsize = narrow_arsize_int;
    assign narrow_arburst = narrow_arburst_int;
    assign narrow_arprot = narrow_arprot_int;
    assign narrow_aruser = narrow_aruser_int;
  end

  if (RegisterWideOutputs) begin : gen_wide_reg
    br_flow_reg_fwd #(
        .Width(IdWidth + BUserWidth + br_amba::AxiRespWidth)
    ) br_flow_reg_fwd_wide_b (
        .clk,
        .rst,
        .push_ready(wide_bready_int),
        .push_valid(wide_bvalid_int),
        .push_data ({wide_bid_int, wide_buser_int, wide_bresp_int}),
        .pop_ready (wide_bready),
        .pop_valid (wide_bvalid),
        .pop_data  ({wide_bid, wide_buser, wide_bresp})
    );

    br_flow_reg_fwd #(
        .Width(IdWidth + WideDataWidth + br_amba::AxiRespWidth + RUserWidth + 1)
    ) br_flow_reg_fwd_wide_r (
        .clk,
        .rst,
        .push_ready(wide_rready_int),
        .push_valid(wide_rvalid_int),
        .push_data ({wide_rid_int, wide_rdata_int, wide_rresp_int, wide_ruser_int, wide_rlast_int}),
        .pop_ready (wide_rready),
        .pop_valid (wide_rvalid),
        .pop_data  ({wide_rid, wide_rdata, wide_rresp, wide_ruser, wide_rlast})
    );
  end else begin : gen_no_wide_reg
    assign wide_bvalid = wide_bvalid_int;
    assign wide_bready_int = wide_bready;
    assign wide_bid = wide_bid_int;
    assign wide_buser = wide_buser_int;
    assign wide_bresp = wide_bresp_int;
    assign wide_rvalid = wide_rvalid_int;
    assign wide_rready_int = wide_rready;
    assign wide_rid = wide_rid_int;
    assign wide_rdata = wide_rdata_int;
    assign wide_rresp = wide_rresp_int;
    assign wide_ruser = wide_ruser_int;
    assign wide_rlast = wide_rlast_int;
  end

  // Implementation assertions
  `BR_ASSERT_IMPL(rd_data_valid_on_r_beat_a, narrow_r_beat |-> read_table_rd_data_valid)
  `BR_ASSERT_IMPL(narrow_r_last_on_beat_last_a,
                  narrow_rvalid_int && narrow_rlast_int |-> r_beat_last)
endmodule
