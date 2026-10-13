// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Incrementing Counter

`include "br_asserts.svh"
`include "br_fv.svh"

module br_counter_incr_fpv_monitor #(
    parameter int MaxValueWidth = 32,
    parameter int MaxIncrementWidth = 32,
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    parameter logic [MaxIncrementWidth-1:0] MaxIncrement = 1,
    parameter bit EnableReinitAndIncr = 1,
    parameter bit EnableSaturate = 0,
    parameter bit EnableWrap = !EnableSaturate,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxIncrementP1Width = MaxIncrementWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int IncrementWidth = $clog2(MaxIncrementP1Width'(MaxIncrement) + 1),
    localparam int SumWidth = ValueWidth + 1
) (
    input logic                      clk,
    input logic                      rst,
    input logic                      reinit,
    input logic [    ValueWidth-1:0] initial_value,
    input logic                      incr_valid,
    input logic [IncrementWidth-1:0] incr,
    input logic [    ValueWidth-1:0] value,
    input logic [    ValueWidth-1:0] value_next
);

  // ----------FV Modeling Code----------
  // EnableSaturate = 1:
  // If overflow, cap at MaxValue

  // EnableWrap = 1:
  // If overflow, wrap around after MaxValue: MaxValue -> 0 -> 1
  // When both modes are disabled, the environment must prevent overflow.
  function automatic logic [ValueWidth-1:0] adjust(input logic [ValueWidth-1:0] base,
                                                   input logic [IncrementWidth-1:0] incr,
                                                   input logic [MaxValueWidth-1:0] max_value);
    logic [ValueWidth:0] base_pad;
    base_pad = {1'b0, base};
    adjust = base_pad + incr > max_value ?  // overflow
    (EnableSaturate ? max_value :
     EnableWrap ? base + incr - max_value - 'd1 : base + incr) : base + incr;
    return adjust;
  endfunction

  logic [ValueWidth-1:0] fv_counter;
  logic [IncrementWidth-1:0] fv_incr;
  logic [ValueWidth-1:0] fv_base;
  logic [IncrementWidth-1:0] fv_applied_incr;
  logic [SumWidth-1:0] fv_sum;

  assign fv_incr = {IncrementWidth{incr_valid}} & incr;
  assign fv_base = reinit ? initial_value : fv_counter;
  assign fv_applied_incr = (reinit && !EnableReinitAndIncr) ? '0 : fv_incr;
  assign fv_sum = SumWidth'(fv_base) + SumWidth'(fv_applied_incr);

  always_ff @(posedge clk) begin
    if (rst) begin
      fv_counter <= initial_value;
    end else if (reinit) begin
      fv_counter <= EnableReinitAndIncr ? adjust(initial_value, fv_incr, MaxValue) : initial_value;
    end else begin
      fv_counter <= adjust(fv_counter, fv_incr, MaxValue);
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME(init_legal_a, reinit |-> initial_value <= MaxValue)
  `BR_ASSUME(incr_legal_a, incr_valid |-> incr <= MaxIncrement)
  if (!EnableWrap && !EnableSaturate) begin : gen_no_overflow
    `BR_ASSUME(no_overflow_a, fv_sum <= SumWidth'(MaxValue))
  end

  // ----------FV assertions----------
  `BR_ASSERT(value_check_a, value == fv_counter)
  `BR_ASSERT(value_sanity_a, value <= MaxValue)
  `BR_ASSERT(value_next_check_a, value_next == adjust(fv_base, fv_applied_incr, MaxValue))
  `BR_ASSERT(value_next_check0_a, !(incr_valid | reinit) |-> value_next == value)
  `BR_ASSERT(value_next_check1_a, incr_valid |=> $past(value_next) == value)

  // ----------Critical Covers----------
  `BR_COVER(reinit_and_change_c, reinit && incr_valid && incr > 0)
  if (EnableWrap || EnableSaturate) begin : gen_overflow
    `BR_COVER(overflow_c, !reinit && fv_sum > SumWidth'(MaxValue))
    if (EnableReinitAndIncr) begin : gen_reinit_overflow
      `BR_COVER(reinit_overflow_c, reinit && fv_sum > SumWidth'(MaxValue))
    end
  end
  if (MaxIncrement < {IncrementWidth{1'b1}}) begin : gen_unused_incr
    `BR_COVER(unused_incr_out_of_range_c, !incr_valid && incr > MaxIncrement)
  end
  if (MaxValue < {ValueWidth{1'b1}}) begin : gen_unused_initial_value
    `BR_COVER(unused_initial_value_out_of_range_c, !reinit && initial_value > MaxValue)
  end

endmodule

bind br_counter_incr br_counter_incr_fpv_monitor #(
    .MaxValueWidth(MaxValueWidth),
    .MaxIncrementWidth(MaxIncrementWidth),
    .MaxValue(MaxValue),
    .MaxIncrement(MaxIncrement),
    .EnableReinitAndIncr(EnableReinitAndIncr),
    .EnableSaturate(EnableSaturate),
    .EnableWrap(EnableWrap),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
