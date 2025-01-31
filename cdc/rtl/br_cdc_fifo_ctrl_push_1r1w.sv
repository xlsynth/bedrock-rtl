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

// Push-side of Bedrock-RTL CDC FIFO Controller (1R1W, Ready/Valid Variant)
//
// The push side of a one-read/one-write (1R1W) asynchronous FIFO controller
// that uses the AMBA-inspired ready-valid handshake protocol for synchronizing
// pipeline stages and stalling when encountering backpressure hazards.
//
// This module is intended to connect to an instance of br_cdc_fifo_ctrl_pop_1r1w
// as well as a 1R1W RAM module.
//
// Ordinarily the push and pop sides of the FIFO controller can be connected
// together directly. If necessary, they can be separated, for example to
// implement a CDC crossing across a boundary where the sending and receiving
// flops must be separated or logic needs to be placed in between the two sides.

`include "br_asserts_internal.svh"

module br_cdc_fifo_ctrl_push_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // The number of push cycles after ram_wr_valid is asserted at which
    // it is safe to read the newly written data.
    parameter int RamWriteLatency = 1,
    // The number of synchronization stages to use for the gray counts.
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
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Push-side interface
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  push_full,
    output logic                  push_full_next,
    output logic [CountWidth-1:0] push_slots,
    output logic [CountWidth-1:0] push_slots_next,

    // Push-side RAM write interface
    output logic                 push_ram_wr_valid,
    output logic [AddrWidth-1:0] push_ram_wr_addr,
    output logic [    Width-1:0] push_ram_wr_data,

    // Posedge-triggered clock.
    input logic pop_clk,
    // Synchronous active-high reset.
    input logic pop_rst,

    // Signals that connect to the pop side.
    input  logic                  pop_reset_active_pop,
    input  logic [CountWidth-1:0] pop_pop_count_gray,
    output logic [CountWidth-1:0] push_push_count_gray,
    output logic                  push_reset_active_push
);
  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [CountWidth-1:0] push_pop_count_gray;
  logic                  push_reset_active_pop;

  br_cdc_fifo_push_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .RamWriteLatency(RamWriteLatency),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_push_ctrl (
      .clk              (push_clk),               // ri lint_check_waive SAME_CLOCK_NAME
      .rst              (push_rst),
      .push_ready,
      .push_valid,
      .push_data,
      .full             (push_full),
      .full_next        (push_full_next),
      .slots            (push_slots),
      .slots_next       (push_slots_next),
      .ram_wr_valid     (push_ram_wr_valid),
      .ram_wr_addr      (push_ram_wr_addr),
      .ram_wr_data      (push_ram_wr_data),
      .push_count_gray  (push_push_count_gray),
      .pop_count_gray   (push_pop_count_gray),
      .reset_active_pop (push_reset_active_pop),
      .reset_active_push(push_reset_active_push)
  );

  br_cdc_fifo_gray_count_sync #(
      .CountWidth(CountWidth),
      .NumStages (NumSyncStages)
  ) br_cdc_fifo_gray_count_sync_pop2push (
      // TODO(zhemao): Remove need for pop_clk and pop_rst here.
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_count_gray(pop_pop_count_gray),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_rst),
      .dst_count_gray(push_pop_count_gray)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_reset_active_pop (
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_bit(pop_reset_active_pop),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_rst),
      .dst_bit(push_reset_active_pop)
  );


  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Check that the FIFO backpressures when it is full.
  `BR_ASSERT_CR_IMPL(push_backpressure_when_full_a, push_full |-> !push_ready, push_clk, push_rst)

endmodule : br_cdc_fifo_ctrl_push_1r1w
