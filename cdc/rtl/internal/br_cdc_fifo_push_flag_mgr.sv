// SPDX-License-Identifier: Apache-2.0

//
// This module manages the push-side flags for a CDC FIFO.
// It takes in the pop count as a gray code, decodes it to binary,
// and compares it to the internal push count to determine the number of
// slots remaining in the FIFO.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_cdc_fifo_push_flag_mgr #(
    parameter int Depth = 2,
    parameter int RamWriteLatency = 1,
    parameter bit RegisterResetActive = 1,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input  logic                  clk,
    input  logic                  rst,
    input  logic                  push_beat,
    output logic [CountWidth-1:0] push_count_gray,
    input  logic [CountWidth-1:0] pop_count_gray,
    output logic [CountWidth-1:0] pop_count_delta,
    output logic [CountWidth-1:0] slots,
    output logic                  full,
    output logic                  reset_active_push,
    input  logic                  reset_active_pop
);
  `BR_ASSERT_STATIC(legal_depth_A, Depth >= 2)
  `BR_ASSERT_STATIC(legal_ram_write_latency_A, RamWriteLatency >= 1)

  localparam int MaxCountP1 = 1 << CountWidth;
  localparam int MaxCount = MaxCountP1 - 1;
  // Need to make sure that on push reset, the updated push_count is not visible
  // to the pop side before reset_active is.
  localparam int PushCountDelay = br_math::max2(RegisterResetActive + 1, RamWriteLatency);

  logic [CountWidth-1:0] push_count;
  logic [CountWidth-1:0] push_count_next;
  logic [CountWidth-1:0] push_count_next_gray;
  logic [CountWidth-1:0] pop_count;
  logic [CountWidth-1:0] pop_count_saved;
  logic [CountWidth-1:0] pop_count_visible;

  br_counter_incr #(
      .MaxValue(MaxCount),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_counter_incr_push_count (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(CountWidth'(1'b0)),
      .incr_valid(push_beat),
      .incr(1'b1),
      .value(push_count),
      .value_next(push_count_next)
  );

  br_enc_gray2bin #(
      .Width(CountWidth)
  ) br_enc_gray2bin_inst (
      .gray(pop_count_gray),
      .bin (pop_count)
  );

  br_enc_bin2gray #(
      .Width(CountWidth)
  ) br_enc_bin2gray_inst (
      .bin (push_count_next),
      .gray(push_count_next_gray)
  );

  br_delay_nr #(
      .Width(1),
      .NumStages(RegisterResetActive)
  ) br_delay_nr_reset_active_push (
      .clk,
      .in(rst),
      .out(reset_active_push),
      .out_stages()
  );

  br_delay #(
      .Width(CountWidth),
      .NumStages(PushCountDelay)
  ) br_delay_push_count_gray (
      .clk,
      .rst,
      .in(push_count_next_gray),
      .out(push_count_gray),
      .out_stages()
  );

  // Extended versions of the counts to allow for overflow
  logic [CountWidth:0] push_count_ext;
  logic [CountWidth:0] pop_count_visible_ext;
  logic [CountWidth:0] items_wrap_offset;
  logic [CountWidth:0] push_count_adjusted;
  logic [CountWidth:0] items_ext;  // ri lint_check_waive INEFFECTIVE_NET

  assign pop_count_visible = reset_active_pop ? pop_count_saved : pop_count;
  assign pop_count_delta = reset_active_pop ? '0 : (pop_count - pop_count_saved);
  assign push_count_ext = {1'b0, push_count};
  assign pop_count_visible_ext = {1'b0, pop_count_visible};
  assign items_wrap_offset = MaxCountP1;
  assign push_count_adjusted = push_count_ext + items_wrap_offset;
  assign items_ext = (push_count_ext >= pop_count_visible_ext) ?
      (push_count_ext - pop_count_visible_ext) :
      (push_count_adjusted - pop_count_visible_ext);
  assign slots = Depth - items_ext[CountWidth-1:0];
  assign full = (slots == '0);

  `BR_REGL(pop_count_saved, pop_count, !reset_active_pop)

  `BR_UNUSED_NAMED(items_msb, items_ext[CountWidth])

  // Implementation checks
  `BR_ASSERT_IMPL(no_overflow_a, items_ext <= Depth)
endmodule : br_cdc_fifo_push_flag_mgr
