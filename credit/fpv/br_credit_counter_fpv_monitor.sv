// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Credit Counter

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_credit_counter_fpv_monitor #(
    parameter int MaxValueWidth = 32,
    parameter int MaxChangeWidth = 32,
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    parameter logic [MaxChangeWidth-1:0] MaxChange = 1,
    parameter logic [MaxChangeWidth-1:0] MaxIncrement = MaxChange,
    parameter logic [MaxChangeWidth-1:0] MaxDecrement = MaxChange,
    parameter bit EnableCoverZeroIncrement = 1,
    parameter bit EnableCoverZeroDecrement = MaxDecrement > 1,
    parameter bit EnableCoverDecrementBackpressure = 1,
    parameter bit EnableCoverWithhold = 1,
    parameter bit EnableAssertAlwaysDecr = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxChangeP1Width = MaxChangeWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int ChangeWidth = $clog2(MaxChangeP1Width'(MaxChange) + 1)
) (
    input logic clk,
    input logic rst,

    input logic                   incr_valid,
    input logic [ChangeWidth-1:0] incr,
    input logic                   decr_ready,
    input logic                   decr_valid,
    input logic [ChangeWidth-1:0] decr,

    input logic [ValueWidth-1:0] initial_value,
    input logic [ValueWidth-1:0] withhold,
    input logic [ValueWidth-1:0] value,
    input logic [ValueWidth-1:0] available
);

  // ----------FV modeling code----------
  logic [ValueWidth:0] fv_credit_cnt;
  logic [ValueWidth-1:0] fv_initial_value;
  logic [ValueWidth-1:0] fv_value;
  logic [ValueWidth-1:0] fv_available;
  logic [ChangeWidth-1:0] fv_incr;
  logic [ChangeWidth-1:0] fv_decr;

  assign fv_incr = {ChangeWidth{incr_valid}} & incr;
  assign fv_decr = {ChangeWidth{decr_valid & decr_ready}} & decr;
  // flop initial_value after rst
  `BR_REGI(fv_initial_value, fv_initial_value, initial_value)
  `BR_REGI(fv_credit_cnt, fv_credit_cnt + fv_incr - fv_decr, MaxValue)
  `BR_REGI(fv_value, fv_value + fv_incr - fv_decr, initial_value)
  assign fv_available = (fv_value + fv_incr) > withhold ? (fv_value + fv_incr - withhold) : 'd0;

  // ----------FV assumptions----------
  `BR_ASSUME(withhold_a, withhold <= MaxValue)
  `BR_ASSUME(incr_a, incr_valid |-> incr <= MaxIncrement)
  `BR_ASSUME(decr_a, decr_valid |-> decr <= MaxDecrement)
  `BR_ASSUME(no_spurious_incr_valid_a,
             incr_valid |-> (fv_credit_cnt + fv_incr - fv_decr) <= MaxValue)
  if (EnableCoverZeroIncrement) begin : gen_assume_zero_increment_ok
    `BR_COVER(zero_increment_c, incr_valid && incr == 'd0)
  end else begin : gen_assume_nonzero_increment
    `BR_ASSUME(nonzero_increment_a, incr_valid |-> incr != 'd0)
  end
  if (EnableCoverZeroDecrement) begin : gen_assume_zero_decrement_ok
    `BR_COVER(zero_decrement_c, decr_valid && decr == 'd0)
  end else begin : gen_assume_nonzero_decrement
    `BR_ASSUME(nonzero_decrement_a, decr_valid |-> decr != 'd0)
  end
  if (EnableCoverDecrementBackpressure) begin : gen_cover_decrement_backpressure
    `BR_COVER(decrement_backpressure_c, decr_valid && decr > fv_available)
  end else begin : gen_assume_no_decrement_backpressure
    `BR_ASSUME(no_decrement_backpressure_a, decr_valid |-> decr <= fv_available)
  end
  if (EnableCoverWithhold) begin : gen_assume_withhold_liveness
    `BR_ASSUME(withold_liveness_a, s_eventually withhold < fv_initial_value)
  end else begin : gen_assume_no_withhold
    `BR_ASSUME(no_withhold_a, withhold == 'd0)
  end
  if (EnableAssertAlwaysDecr) begin : gen_assume_always_decr
    `BR_ASSUME(always_decr_a, decr_valid)
  end else begin : gen_cover_no_decr
    `BR_COVER(no_decr_c, !decr_valid)
  end

  // ----------FV assertions----------
  // Always-decrement with no backpressure requires each decrement to be immediately serviceable,
  // so the counter cannot be empty without an increment to replenish available credit.
  if (!(EnableAssertAlwaysDecr && !EnableCoverDecrementBackpressure)) begin : gen_decr_ready_sanity
    `BR_ASSERT(decr_ready_sanity_a, (fv_credit_cnt == 'd0) && (fv_incr == 'd0) |-> fv_decr == 'd0)
  end
  // Cover the ready contract for all serviceable decrement requests, including decr == 0.
  `BR_ASSERT(decr_ready_forward_progress_a, decr_valid && decr <= fv_available |-> decr_ready)
  `BR_ASSERT(value_a, fv_value == value)
  `BR_ASSERT(available_a, fv_available == available)
  `BR_ASSERT(available_liveness_a, (fv_decr != 'd0) |-> s_eventually (fv_available != 'd0))

endmodule : br_credit_counter_fpv_monitor

bind br_credit_counter br_credit_counter_fpv_monitor #(
    .MaxValueWidth(MaxValueWidth),
    .MaxChangeWidth(MaxChangeWidth),
    .MaxValue(MaxValue),
    .MaxChange(MaxChange),
    .MaxIncrement(MaxIncrement),
    .MaxDecrement(MaxDecrement),
    .EnableCoverZeroIncrement(EnableCoverZeroIncrement),
    .EnableCoverZeroDecrement(EnableCoverZeroDecrement),
    .EnableCoverDecrementBackpressure(EnableCoverDecrementBackpressure),
    .EnableCoverWithhold(EnableCoverWithhold),
    .EnableAssertAlwaysDecr(EnableAssertAlwaysDecr),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
