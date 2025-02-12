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

// br_credit_sender FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_credit_sender_fpv_monitor #(
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least 1.
    parameter int MaxCredit = 1,
    // If 1, add 1 cycle of retiming to pop outputs.
    parameter bit RegisterPopOutputs = 0,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int CounterWidth = $clog2(MaxCredit + 1)
) (
    input logic clk,
    input logic rst,

    // Ready/valid push interface.
    input logic push_ready,
    input logic push_valid,
    input logic [Width-1:0] push_data,

    // Credit/valid pop interface.
    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic pop_credit,
    input logic pop_valid,
    input logic [Width-1:0] pop_data,

    // Reset value for the credit counter
    input logic [CounterWidth-1:0] credit_initial,
    // Dynamically withhold credits from circulation
    input logic [CounterWidth-1:0] credit_withhold,
    // Credit counter state before increment/decrement/withhold.
    input logic [CounterWidth-1:0] credit_count,
    // Dynamic amount of available credit.
    input logic [CounterWidth-1:0] credit_available
);

  // ----------FV modeling code----------
  logic fv_rst;
  logic [CounterWidth-1:0] fv_pop_credit_cnt;
  logic [CounterWidth-1:0] fv_max_credit;

  assign fv_rst = rst | pop_receiver_in_reset;
  `BR_REGIX(fv_pop_credit_cnt, fv_pop_credit_cnt + pop_credit - pop_valid, credit_initial, clk,
            fv_rst)
  `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial, clk, fv_rst)

  // ----------FV assumptions----------
  `BR_ASSUME(pop_receiver_in_reset_a, !pop_receiver_in_reset |=> !pop_receiver_in_reset)
  `BR_ASSUME(credit_withhold_a, credit_withhold <= MaxCredit)
  `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold < fv_max_credit))
  `BR_ASSUME(push_valid_ready_a, push_valid && !push_ready |=> push_valid && $stable(push_data))
  `BR_ASSUME(no_spurious_pop_credit_a,
             (fv_pop_credit_cnt == fv_max_credit) |-> pop_valid == pop_credit)

  // ----------FV assertions----------
  `BR_ASSERT(push_valid_deadlock_a, push_valid |-> s_eventually push_ready)
  `BR_ASSERT(no_spurious_pop_valid_a, (fv_pop_credit_cnt == 'd0) && !pop_credit |-> !pop_valid)
  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxCredit)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid & push_ready),
      .incoming_data(push_data),
      .outgoing_vld(pop_valid),
      .outgoing_data(pop_data)
  );

endmodule : br_credit_sender_fpv_monitor

bind br_credit_sender br_credit_sender_fpv_monitor #(
    .Width(Width),
    .MaxCredit(MaxCredit),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
