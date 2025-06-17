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

// Bedrock-RTL Credit Counter

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_credit_counter_fpv_monitor #(
    parameter int MaxValueWidth = 32,
    parameter int MaxChangeWidth = 32,
    parameter logic [MaxValueWidth-1:0] MaxValue = 1,
    parameter logic [MaxChangeWidth-1:0] MaxChange = 1,
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
  `BR_ASSUME(incr_a, incr_valid |-> incr <= MaxChange)
  `BR_ASSUME(decr_a, decr_valid |-> decr <= MaxChange)
  `BR_ASSUME(no_spurious_incr_valid_a, (fv_credit_cnt + incr - fv_decr) > MaxValue |-> !incr_valid)
  `BR_ASSUME(withold_liveness_a, s_eventually withhold < fv_initial_value)

  // ----------FV assertions----------
  `BR_ASSERT(decr_ready_sanity_a, (fv_credit_cnt == 'd0) && (fv_incr == 'd0) |-> fv_decr == 'd0)
  `BR_ASSERT(decr_ready_forward_progress_a,
             (decr_valid && fv_available >= decr && fv_available != 'd0) |-> decr_ready)
  `BR_ASSERT(value_a, fv_value == value)
  `BR_ASSERT(available_a, fv_available == available)
  `BR_ASSERT(available_liveness_a, (fv_decr != 'd0) |-> s_eventually (fv_available != 'd0))

endmodule : br_credit_counter_fpv_monitor

bind br_credit_counter br_credit_counter_fpv_monitor #(
    .MaxValueWidth(MaxValueWidth),
    .MaxChangeWidth(MaxChangeWidth),
    .MaxValue(MaxValue),
    .MaxChange(MaxChange),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
