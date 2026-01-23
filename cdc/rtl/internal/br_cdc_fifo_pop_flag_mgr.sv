// SPDX-License-Identifier: Apache-2.0

//
// This module manages the pop-side flags for a CDC FIFO.
// It takes in the push count as a gray code, decodes it to binary,
// and compares it to the internal pop count to determine the number of
// items in the FIFO.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_cdc_fifo_pop_flag_mgr #(
    parameter int Depth = 2,
    parameter bit RegisterResetActive = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input  logic                  clk,
    input  logic                  rst,
    input  logic                  pop_beat,
    input  logic [CountWidth-1:0] push_count_gray,
    output logic [CountWidth-1:0] pop_count_gray,
    output logic [CountWidth-1:0] items,
    output logic                  empty,
    input  logic                  reset_active_push,
    output logic                  reset_active_pop
);
  `BR_ASSERT_STATIC(legal_depth_A, Depth >= 2)

  br_cdc_fifo_reset_overlap_checks br_cdc_fifo_reset_overlap_checks (
      .clk,
      .reset_active_push,
      .reset_active_pop
  );

  localparam int MaxCountP1 = 1 << CountWidth;
  localparam int MaxCount = MaxCountP1 - 1;
  // Need to make sure that on pop reset, the updated pop_count is not visible
  // to the push side before reset_active is.
  localparam int PopCountDelay = RegisterResetActive + 1;

  logic [CountWidth-1:0] pop_count;
  logic [CountWidth-1:0] pop_count_next;
  logic [CountWidth-1:0] pop_count_next_gray;
  logic [CountWidth-1:0] push_count;
  logic [CountWidth-1:0] push_count_saved;
  logic [CountWidth-1:0] push_count_visible;

  br_counter_incr #(
      .MaxValue(MaxCount),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableCoverZeroIncrement(0),
      .EnableCoverReinit(0)
  ) br_counter_incr_pop_count (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(CountWidth'(1'b0)),
      .incr_valid(pop_beat),
      .incr(1'b1),
      .value(pop_count),
      .value_next(pop_count_next)
  );

  br_enc_gray2bin #(
      .Width(CountWidth)
  ) br_enc_gray2bin_inst (
      .gray(push_count_gray),
      .bin (push_count)
  );

  br_enc_bin2gray #(
      .Width(CountWidth)
  ) br_enc_bin2gray_inst (
      .bin (pop_count_next),
      .gray(pop_count_next_gray)
  );

  br_delay_nr #(
      .Width(1),
      .NumStages(RegisterResetActive)
  ) br_delay_nr_reset_active_pop (
      .clk,
      .in(rst),
      .out(reset_active_pop),
      .out_stages()
  );

  br_delay_nr #(
      .Width(CountWidth),
      .NumStages(PopCountDelay)
  ) br_delay_nr_pop_count_gray (
      .clk,
      .in(pop_count_next_gray),
      .out(pop_count_gray),
      .out_stages()
  );

  // Extended versions of the counts to allow for overflow
  logic [CountWidth:0] pop_count_ext;
  logic [CountWidth:0] push_count_visible_ext;
  logic [CountWidth:0] items_ext;  // ri lint_check_waive INEFFECTIVE_NET
  logic [CountWidth:0] items_wrap_offset;
  logic [CountWidth:0] push_count_adjusted;

  assign push_count_visible = reset_active_push ? push_count_saved : push_count;
  assign pop_count_ext = {1'b0, pop_count};
  assign push_count_visible_ext = {1'b0, push_count_visible};
  assign items_wrap_offset = MaxCountP1;
  assign push_count_adjusted = push_count_visible_ext + items_wrap_offset;
  assign items_ext = (push_count_visible_ext >= pop_count_ext) ?
      (push_count_visible_ext - pop_count_ext) :
      (push_count_adjusted - pop_count_ext);
  assign items = items_ext[CountWidth-1:0];
  assign empty = (items == '0);

  `BR_REGL(push_count_saved, push_count, !reset_active_push)

  `BR_UNUSED_NAMED(items_msb, items_ext[CountWidth]);

  // Implementation checks
  `BR_ASSERT_IMPL(no_items_overflow_A, items_ext <= Depth)

endmodule : br_cdc_fifo_pop_flag_mgr
