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

// Basic FPV checks for all CDC FIFO variations

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_basic_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // Number of synchronization stages to use for the gray counts. Must be >=2.
    parameter int NumSyncStages = 3,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter int RamWriteLatency = 1,
    parameter int RamReadLatency = 1,
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    // Push-side interface.
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_ready,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic             pop_clk,
    input logic             pop_rst,
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic push_full,
    input logic [CountWidth-1:0] push_slots,

    // Pop-side status flags
    input logic pop_empty,
    input logic [CountWidth-1:0] pop_items
);

  localparam int ResetActiveDelay = 1;
  // Need to make sure that on push reset, the updated push_count is not visible
  // to the pop side before reset_active is.
  localparam int PushCountDelay = (ResetActiveDelay + 1) >= RamWriteLatency ?
  (ResetActiveDelay + 1) : RamWriteLatency;
  // Need to make sure that on pop reset, the updated pop_count is not visible
  // to the push side before reset_active is.
  localparam int PopCountDelay = ResetActiveDelay + 1;

  // ----------FV assumptions----------
  `BR_ASSUME_CR(pop_ready_liveness_a, s_eventually (pop_ready), pop_clk, pop_rst)
  if (EnableAssertPushValidStability) begin : gen_push_valid_stable
    `BR_ASSUME_CR(push_valid_stable_a, push_valid && !push_ready |=> push_valid, push_clk, push_rst)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data_stable
    `BR_ASSUME_CR(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data), push_clk,
                  push_rst)
  end

  // ----------FV Modeling Code----------
  logic push_vr;
  logic pop_vr;
  logic fv_push_full;
  logic fv_pop_empty;
  logic [CountWidth-1:0] fv_push_items, fv_push_slots;
  logic [CountWidth-1:0] fv_pop_items;

  // pop side info
  localparam int CW = 32;  //FV CountWidth;
  logic [CW-1:0] fv_pop_cnt;
  logic [CW-1:0] fv_pop_sync;
  logic [CW-1:0] fv_pop_sync_cnt;
  // push side info
  logic [CW-1:0] fv_push_cnt;
  logic [CW-1:0] fv_push_sync;
  logic [CW-1:0] fv_push_sync_cnt;

  assign push_vr = push_valid & push_ready;
  assign pop_vr  = pop_valid & pop_ready;
  // count number of valid push at push side
  `BR_REGX(fv_push_cnt, fv_push_cnt + push_vr, push_clk, push_rst)
  // count number of valid pop at pop side
  `BR_REGX(fv_pop_cnt, fv_pop_cnt + pop_vr, pop_clk, pop_rst)

  // number of valid pop synced to push side
  fv_delay #(
      .Width(CW),
      .NumStages(PopCountDelay - 1)  // -1 since fv_pop_cnt is flopped
  ) delay_pop_vr (
      .clk(pop_clk),
      .rst(pop_rst),
      .in (fv_pop_cnt),
      .out(fv_pop_sync)
  );

  fv_delay #(
      .Width(CW),
      .NumStages(NumSyncStages + 1)
  ) delay_pop_sync (
      .clk(push_clk),
      .rst(push_rst),
      .in (fv_pop_sync),
      .out(fv_pop_sync_cnt)
  );

  // number of valid push synced to pop side
  fv_delay #(
      .Width(CW),
      .NumStages(PushCountDelay - 1)  // -1 since fv_push_cnt is flopped
  ) delay_push_vr (
      .clk(push_clk),
      .rst(push_rst),
      .in (fv_push_cnt),
      .out(fv_push_sync)
  );

  fv_delay #(
      .Width(CW),
      .NumStages(NumSyncStages + 1)
  ) delay_push_sync (
      .clk(pop_clk),
      .rst(pop_rst),
      .in (fv_push_sync),
      .out(fv_push_sync_cnt)
  );

  assign fv_push_items = fv_push_cnt - fv_pop_sync_cnt;
  assign fv_push_slots = Depth - fv_push_items;
  assign fv_pop_items  = fv_push_sync_cnt - fv_pop_cnt;

  assign fv_push_full  = fv_push_items == Depth;
  assign fv_pop_empty  = fv_pop_items == 'd0;

  // ----------Sanity Check----------
  `BR_ASSERT_CR(no_ready_when_full_a, push_full |-> !push_ready, push_clk, push_rst)
  `BR_ASSERT_CR(no_pop_when_empty_a, pop_empty |-> !pop_valid, pop_clk, pop_rst)
  `BR_ASSERT_CR(pop_valid_ready_a, pop_valid && !pop_ready |=> pop_valid && $stable(pop_data),
                pop_clk, pop_rst)

  // empty, full check
  `BR_ASSERT_CR(push_full_a, fv_push_full == push_full, push_clk, push_rst)
  `BR_ASSERT_CR(pop_empty_a, fv_pop_empty == pop_empty, pop_clk, pop_rst)

  // slots, items check
  `BR_ASSERT_CR(pop_items_a, fv_pop_items == pop_items, pop_clk, pop_rst)
  `BR_ASSERT_CR(push_slots_a, fv_push_slots == push_slots, push_clk, push_rst)

  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(0),
      .MAX_PENDING(Depth)
  ) scoreboard (
      .incoming_clk(push_clk),
      .outgoing_clk(pop_clk),
      .rstN(!rst),
      .incoming_vld(push_vr),
      .incoming_data(push_data),
      .outgoing_vld(pop_vr),
      .outgoing_data(pop_data)
  );

  // ----------Forward Progress Check----------
  if (EnableAssertPushValidStability) begin : gen_stable
    `BR_ASSERT(no_deadlock_pop_a, push_valid |-> s_eventually pop_valid)
  end else begin : gen_not_stable
    `BR_ASSERT(no_deadlock_pop_a, push_vr |-> s_eventually pop_valid)
  end

  // ----------Critical Covers----------
  `BR_COVER_CR(fifo_full_c, push_full, push_clk, push_rst)

endmodule : br_cdc_fifo_basic_fpv_monitor
