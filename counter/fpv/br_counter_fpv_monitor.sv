// Copyright 2024-2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Increment/Decrement Counter w/ Overflow Handling

`include "br_asserts.svh"
`include "br_fv.svh"

module br_counter_fpv_monitor #(
    parameter int MaxValueWidth = 32,
    parameter int MaxChangeWidth = 32,
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    parameter logic [MaxChangeWidth-1:0] MaxChange = 1,
    parameter bit EnableWrap = 1,
    parameter bit EnableReinitAndChange = 1,
    parameter bit EnableSaturate = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int MaxValueP1Width = MaxValueWidth + 1,
    localparam int MaxChangeP1Width = MaxChangeWidth + 1,
    localparam int ValueWidth = $clog2(MaxValueP1Width'(MaxValue) + 1),
    localparam int ChangeWidth = $clog2(MaxChangeP1Width'(MaxChange) + 1)
) (
    input logic                   clk,
    input logic                   rst,
    input logic                   reinit,
    input logic [ ValueWidth-1:0] initial_value,
    input logic                   incr_valid,
    input logic [ChangeWidth-1:0] incr,
    input logic                   decr_valid,
    input logic [ChangeWidth-1:0] decr,
    input logic [ ValueWidth-1:0] value,
    input logic [ ValueWidth-1:0] value_next
);

  // ----------FV Modeling Code----------
  // EnableWrap = 1:
  // If overflow, wrap around after MaxValue: MaxValue -> 0 -> 1
  // If underflow, wrap around after 0: 0 -> MaxValue -> MaxValue-1

  // EnableSaturate = 1:
  // If overflow, cap at MaxValue
  // If underflow, stop at 0

  // {EnableWrap, EnableSaturate} can be all combinations but not {1,1}
  function automatic logic [ValueWidth-1:0] adjust(
      input logic [ValueWidth-1:0] base, input logic [ChangeWidth-1:0] incr,
      input logic [ChangeWidth-1:0] decr, input logic [MaxValueWidth-1:0] max_value);
    logic overflow, underflow;
    logic [ValueWidth:0] base_pad;
    base_pad = {1'b0, base};
    overflow = (incr > decr) && (base_pad + incr - decr > max_value);
    underflow = (incr < decr) && (base_pad + incr - decr > base);
    adjust = overflow ?
               (EnableSaturate ? max_value : base + incr - decr - max_value - 'd1) :
               underflow ?
               (EnableSaturate ? 'd0 : base + incr - decr + max_value + 'd1):
               base + incr - decr;
    return adjust;
  endfunction

  logic [ ValueWidth-1:0] fv_counter;
  logic [ChangeWidth-1:0] fv_incr;
  logic [ChangeWidth-1:0] fv_decr;

  assign fv_incr = {ChangeWidth{incr_valid}} & incr;
  assign fv_decr = {ChangeWidth{decr_valid}} & decr;

  always_ff @(posedge clk) begin
    if (rst) begin
      fv_counter <= initial_value;
    end else if (reinit) begin
      fv_counter <= EnableReinitAndChange ? adjust(initial_value, fv_incr, fv_decr, MaxValue) :
          initial_value;
    end else begin
      fv_counter <= adjust(fv_counter, fv_incr, fv_decr, MaxValue);
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME(init_legal_a, initial_value <= MaxValue)
  `BR_ASSUME(incr_legal_a, incr <= MaxChange)
  `BR_ASSUME(decr_legal_a, decr <= MaxChange)

  // only when EnableWrap and EnableSaturate are both 0s, counter doesn't handle overflow/underflow
  if (!EnableWrap && !EnableSaturate) begin : gen_no_over_underflow
    // for reinit and change
    if (EnableReinitAndChange) begin : gen_reinit_change
      `BR_ASSUME(no_overflow_init_a,
                 reinit && (fv_incr > fv_decr) |-> initial_value + fv_incr - fv_decr <= MaxValue)
      `BR_ASSUME(
          no_underflow_init_a,
          reinit && (fv_decr > fv_incr) |-> initial_value + fv_incr - fv_decr < initial_value)
    end
    // normal case
    `BR_ASSUME(no_overflow_a, fv_incr > fv_decr |-> fv_counter + fv_incr - fv_decr <= MaxValue)
    `BR_ASSUME(no_underflow_a, fv_decr > fv_incr |-> fv_counter + fv_incr - fv_decr < fv_counter)
  end

  // ----------FV assertions----------
  `BR_ASSERT(value_check_a, value == fv_counter)
  `BR_ASSERT(value_sanity_a, value <= MaxValue)
  `BR_ASSERT(value_next_check0_a, !(incr_valid | decr_valid | reinit) |-> value_next == value)
  `BR_ASSERT(value_next_check1_a, incr_valid | decr_valid |=> $past(value_next) == value)
  if (!EnableWrap && !EnableSaturate) begin : gen_no_over_underflow_check
    `BR_ASSERT(no_overflow_check_a, (fv_incr > fv_decr) && !reinit |-> value_next > value)
    `BR_ASSERT(no_underflow_check_a, (fv_decr > fv_incr) && !reinit |-> value_next < value)
  end

  // ----------Critical Covers----------
  `BR_COVER(reinit_and_change_c, reinit && (incr_valid || decr_valid))
  // when EnableWrap or EnableSaturate is 1, counter handles overflow/underflow
  if (EnableWrap | EnableSaturate) begin : gen_over_underflow
    // The cover shows up as unreachable if MaxValue is the largest number that
    // can be represented. Just disable it in this case.
    // TODO(zhemao): Figure out how to get this to work
    if (MaxValue != {MaxValueWidth{1'b1}}) begin : gen_cover_overflow
      `BR_COVER(overflow_c, (fv_decr < fv_incr) && (value + fv_incr - fv_decr > MaxValue))
    end
    `BR_COVER(underflow_c, (fv_decr > fv_incr) && (value < (fv_decr - fv_incr)))
  end

endmodule : br_counter_fpv_monitor

bind br_counter br_counter_fpv_monitor #(
    .MaxValueWidth(MaxValueWidth),
    .MaxChangeWidth(MaxChangeWidth),
    .MaxValue(MaxValue),
    .MaxChange(MaxChange),
    .EnableWrap(EnableWrap),
    .EnableReinitAndChange(EnableReinitAndChange),
    .EnableSaturate(EnableSaturate),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
