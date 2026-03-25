
// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL AXI Resizer Beat Tracker
//
// This helper module keeps track of the current offset and beat ID while
// resizing an AXI transaction. The offset is needed to determine which lane
// of the wide data a narrow data beat corresponds to. The beat ID is needed
// to determine when a narrow beat is the last in a wide beat.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_amba_axi_resizer_beat_tracker #(
    parameter int WideBytes   = 2,
    parameter int NarrowBytes = 1,

    localparam int WideSizeLog2 = $clog2(WideBytes),
    localparam int NarrowSizeLog2 = $clog2(NarrowBytes),
    localparam int LanesPerWide = WideBytes / NarrowBytes,
    localparam int LaneSelWidth = br_math::clamped_clog2(LanesPerWide),
    localparam int ByteOffsetWidth = br_math::clamped_clog2(WideBytes),
    localparam int MaxShift = WideSizeLog2 - NarrowSizeLog2,
    localparam int ShiftWidth = $clog2(MaxShift + 1)
) (
    input logic clk,
    input logic rst,

    input logic start_valid,
    input logic [ByteOffsetWidth-1:0] start_offset,
    input logic [br_amba::AxiBurstSizeWidth-1:0] size,
    input br_amba::axi_burst_type_t burst,
    input logic [ShiftWidth-1:0] shift,

    input logic beat_valid,
    output logic [LaneSelWidth-1:0] beat_lane,
    output logic beat_last
);
  // Internal integration checks
  `BR_ASSERT_IMPL(shift_in_range_a, start_valid |-> shift <= MaxShift)
  `BR_ASSERT_IMPL(size_in_range_a, start_valid |-> size <= NarrowSizeLog2)

  // Implementation

  logic [br_amba::AxiBurstSizeWidth-1:0] size_reg;
  br_amba::axi_burst_type_t burst_reg;
  logic [ShiftWidth-1:0] shift_reg;
  logic [2**ShiftWidth-1:0] beats_per_wide;
  logic [2**ShiftWidth-1:0] beats_per_wide_minus1_ext;
  logic [LaneSelWidth-1:0] beats_per_wide_minus1;

  `BR_REGL(size_reg, size, start_valid)
  `BR_REGLI(burst_reg, burst, start_valid, br_amba::AxiBurstReserved)
  `BR_REGL(shift_reg, shift, start_valid)

  // ri lint_check_waive VAR_SHIFT
  assign beats_per_wide = 1'b1 << shift_reg;
  assign beats_per_wide_minus1_ext = beats_per_wide - 1'b1;
  assign beats_per_wide_minus1 = beats_per_wide_minus1_ext[LaneSelWidth-1:0];
  `BR_UNUSED_NAMED(beats_per_wide_minus1_ext_msbs,
                   beats_per_wide_minus1_ext[2**ShiftWidth-1:LaneSelWidth])

  // We need to keep track of the current offset so that we know which lane of
  // the wide data corresponds to the current narrow beat.
  // The offset is initialized from the original offset.
  // For non-fixed bursts, it should increment by 2 ** size each time.
  localparam int BeatOffsetIncrWidth = $clog2(NarrowBytes + 1);
  logic [ByteOffsetWidth-1:0] beat_offset;
  logic beat_offset_incr_valid;
  logic [2**br_amba::AxiBurstSizeWidth-1:0] beat_offset_incr_ext;
  logic [BeatOffsetIncrWidth-1:0] beat_offset_incr;
  logic [ByteOffsetWidth-1:0] beat_offset_init_value;

  // Don't increment the offset for fixed burst type
  assign beat_offset_incr_valid = beat_valid && burst_reg != br_amba::AxiBurstFixed;
  // ri lint_check_waive VAR_SHIFT
  assign beat_offset_incr_ext = 1'b1 << size_reg;
  assign beat_offset_incr = beat_offset_incr_ext[BeatOffsetIncrWidth-1:0];
  assign beat_offset_init_value = rst ? '0 : start_offset;

  br_counter_incr #(
      .MaxValue(WideBytes - 1),
      .MaxIncrement(NarrowBytes),
      // When initializing, we don't want to take the increment
      .EnableReinitAndIncr(0),
      .EnableCoverZeroIncrement(0)
  ) br_counter_incr_beat_offset (
      .clk,
      .rst,
      .reinit(start_valid),
      .initial_value(beat_offset_init_value),
      .incr_valid(beat_offset_incr_valid),
      .incr(beat_offset_incr),
      .value(beat_offset),
      .value_next()
  );

  assign beat_lane = beat_offset[WideSizeLog2-1:NarrowSizeLog2];

  `BR_UNUSED_NAMED(beat_offset_incr_ext_msbs,
                   beat_offset_incr_ext[2**br_amba::AxiBurstSizeWidth-1:BeatOffsetIncrWidth])
  if (NarrowSizeLog2 > 0) begin : gen_unused_beat_offset_lsbs
    `BR_UNUSED_NAMED(beat_offset_lsbs, beat_offset[NarrowSizeLog2-1:0])
  end

  // The beat ID counter tracks which narrow beat within the wide beat we are on.
  // Always reinit at 0 and wraparound once we reach beats_per_wide_minus1.
  logic [LaneSelWidth-1:0] beat_id;
  logic reinit_beat_id;

  assign reinit_beat_id = start_valid || (beat_valid && beat_id == beats_per_wide_minus1);
  assign beat_last = beat_id == beats_per_wide_minus1;

  br_counter_incr #(
      .MaxValue(LanesPerWide - 1),
      .MaxIncrement(1),
      .EnableReinitAndIncr(0),
      .EnableCoverZeroIncrement(0),
      // reinit will be always be asserted before the counter wraps around
      .EnableWrap(0)
  ) br_counter_incr_beat_id (
      .clk,
      .rst,
      .reinit(reinit_beat_id),
      .initial_value('0),
      .incr_valid(beat_valid),
      .incr(1'b1),
      .value(beat_id),
      .value_next()
  );

  // Implementation assertions
  `BR_ASSERT_IMPL(beats_per_wide_minus1_ext_msbs_zero_a,
                  beats_per_wide_minus1_ext[2**ShiftWidth-1:LaneSelWidth] == '0)
  `BR_ASSERT_IMPL(beat_offset_incr_ext_msbs_zero_a,
                  beat_offset_incr_ext[2**br_amba::AxiBurstSizeWidth-1:BeatOffsetIncrWidth] == '0)
endmodule
