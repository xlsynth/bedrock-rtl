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

// Bedrock-RTL Incrementing Counter

`include "br_asserts.svh"
`include "br_fv.svh"

module br_counter_incr_fpv_monitor #(
    parameter int MaxValue = 1,  // Must be at least 1. Inclusive. Also the initial value.
    parameter int MaxIncrement = 1,  // Must be at least 1 and at most MaxValue. Inclusive.
    parameter bit EnableReinitAndIncr = 1,
    parameter bit EnableSaturate = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int IncrementWidth = $clog2(MaxIncrement + 1)
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

  // EnableSaturate = 0:
  // If overflow, wrap around after MaxValue: MaxValue -> 0 -> 1
  function automatic logic [ValueWidth-1:0] adjust(input logic [ValueWidth-1:0] base,
                                                   input logic [IncrementWidth-1:0] incr,
                                                   input int max_value);
    logic [ValueWidth:0] base_pad;
    base_pad = {1'b0, base};
    adjust = base_pad + incr > MaxValue ?  // overflow
    (EnableSaturate ? MaxValue : base + incr - max_value - 'd1) : base + incr;
    return adjust;
  endfunction

  logic [ValueWidth-1:0] fv_counter;
  logic [IncrementWidth-1:0] fv_incr;

  assign fv_incr = {IncrementWidth{incr_valid}} & incr;

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
  `BR_ASSUME(init_legal_a, initial_value <= MaxValue)
  `BR_ASSUME(incr_legal_a, incr <= MaxIncrement)

  // ----------FV assertions----------
  `BR_ASSERT(value_check_a, value == fv_counter)
  `BR_ASSERT(value_sanity_a, value <= MaxValue)
  `BR_ASSERT(value_next_check0_a, !(incr_valid | reinit) |-> value_next == value)
  `BR_ASSERT(value_next_check1_a, incr_valid |=> $past(value_next) == value)

  // ----------Critical Covers----------
  `BR_COVER(reinit_and_change_c, reinit && incr_valid)
  `BR_COVER(overflow_c, fv_counter + fv_incr > MaxValue)

endmodule

bind br_counter_incr br_counter_incr_fpv_monitor #(
    .MaxValue(MaxValue),
    .MaxIncrement(MaxIncrement),
    .EnableReinitAndIncr(EnableReinitAndIncr),
    .EnableSaturate(EnableSaturate),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
