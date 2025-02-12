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

// Bedrock-RTL Decrementing Counter

`include "br_asserts.svh"
`include "br_fv.svh"

module br_counter_decr_fpv_monitor #(
    parameter int MaxValue = 1,  // Must be at least 1. Inclusive. Also the initial value.
    parameter int MaxDecrement = 1,  // Must be at least 1 and at most MaxValue. Inclusive.
    parameter bit EnableReinitAndDecr = 1,
    parameter bit EnableSaturate = 0,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int DecrementWidth = $clog2(MaxDecrement + 1)
) (
    input logic                      clk,
    input logic                      rst,
    input logic                      reinit,
    input logic [    ValueWidth-1:0] initial_value,
    input logic                      decr_valid,
    input logic [DecrementWidth-1:0] decr,
    input logic [    ValueWidth-1:0] value,
    input logic [    ValueWidth-1:0] value_next
);

  // ----------FV Modeling Code----------
  // EnableSaturate = 1:
  // If underflow, stop at 0

  // EnableSaturate = 0:
  // If underflow, wrap around after 0: 0 -> MaxValue -> MaxValue-1
  function automatic logic [ValueWidth-1:0] adjust(input logic [ValueWidth-1:0] base,
                                                   input logic [DecrementWidth-1:0] decr,
                                                   input int max_value);

    adjust = base < decr ?  // underflow
    (EnableSaturate ? 'd0 : base - decr + max_value + 'd1) : base - decr;
    return adjust;
  endfunction

  logic [ValueWidth-1:0] fv_counter;
  logic [DecrementWidth-1:0] fv_decr;

  assign fv_decr = {DecrementWidth{decr_valid}} & decr;

  always_ff @(posedge clk) begin
    if (rst) begin
      fv_counter <= initial_value;
    end else if (reinit) begin
      fv_counter <= EnableReinitAndDecr ? adjust(initial_value, fv_decr, MaxValue) : initial_value;
    end else begin
      fv_counter <= adjust(fv_counter, fv_decr, MaxValue);
    end
  end

  // ----------FV assumptions----------
  `BR_ASSUME(init_legal_a, initial_value <= MaxValue)
  `BR_ASSUME(decr_legal_a, decr <= MaxDecrement)

  // ----------FV assertions----------
  `BR_ASSERT(value_check_a, value == fv_counter)
  `BR_ASSERT(value_sanity_a, value <= MaxValue)
  `BR_ASSERT(value_next_check0_a, !(decr_valid | reinit) |-> value_next == value)
  `BR_ASSERT(value_next_check1_a, decr_valid |=> $past(value_next) == value)

  // ----------Critical Covers----------
  `BR_COVER(reinit_and_change_c, reinit && decr_valid)
  `BR_COVER(underflow_c, fv_counter < fv_decr)

endmodule

bind br_counter_decr br_counter_decr_fpv_monitor #(
    .MaxValue(MaxValue),
    .MaxDecrement(MaxDecrement),
    .EnableReinitAndDecr(EnableReinitAndDecr),
    .EnableSaturate(EnableSaturate),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
