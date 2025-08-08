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

// Push-side of Bedrock-RTL CDC FIFO Controller (1R1W, Push Credit/Valid)
//
// The push-side of a one-read/one-write (1R1W) asynchronous FIFO controller
// that uses a credit-valid push interface and an AMBA-inspired ready-valid pop
// interface for synchronizing pipeline stages and stalling when encountering
// backpressure hazards.
//
// This module is intended to connect to an instance of br_cdc_fifo_ctrl_pop_1r1w
// as well as a 1R1W RAM module.
//
// Ordinarily the push and pop sides of the FIFO controller can be connected
// together directly. If necessary, they can be separated, for example to
// implement a CDC crossing across a boundary where the sending and receiving
// flops must be separated or logic needs to be placed in between the two sides.

`include "br_asserts_internal.svh"

module br_cdc_fifo_ctrl_push_1r1w_push_credit #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // The number of push cycles after ram_wr_valid is asserted at which
    // it is safe to read the newly written data.
    parameter int RamWriteLatency = 1,
    // The number of synchronization stages to use for the gray counts.
    parameter int NumSyncStages = 3,
    // Maximum credit for the internal credit counter. Must be at least Depth.
    // Recommended to not override the default because it is the smallest viable size.
    // Overriding may be convenient if having a consistent credit counter register width
    // (say, 16-bit) throughout a design is deemed useful.
    parameter int MaxCredit = Depth,
    // If 1, add a retiming stage to the push_credit signal so that it is
    // driven directly from a flop. This comes at the expense of one additional
    // push cycle of credit loop latency.
    parameter bit RegisterPushOutputs = 0,
    // If 1 (the default), register push_rst on push_clk before sending it out
    // as push_reset_active_push. This adds an extra cycle to the cut-through
    // latency of the FIFO.
    // Do not set this to 0 unless either push_rst is driven directly by a
    // register or if push_reset_active_push is registered externally
    // before synchronization to the pop clock domain. You also cannot set this
    // to 0 if push_sender_in_reset is not tied to 0.
    parameter bit RegisterResetActive = 1,
    // If 1, cover that credit_withhold can be non-zero.
    // Otherwise, assert that it is always zero.
    parameter bit EnableCoverCreditWithhold = 1,
    // If 1, cover that push_sender_in_reset can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushSenderInReset = 1,
    // If 1, cover that push_credit_stall can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushCreditStall = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Push-side interface
    input  logic             push_sender_in_reset,
    output logic             push_receiver_in_reset,
    input  logic             push_credit_stall,
    output logic             push_credit,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  push_full,
    output logic [CountWidth-1:0] push_slots,

    // Push-side credits
    input  logic [CreditWidth-1:0] credit_initial_push,
    input  logic [CreditWidth-1:0] credit_withhold_push,
    output logic [CreditWidth-1:0] credit_count_push,
    output logic [CreditWidth-1:0] credit_available_push,

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

  br_cdc_fifo_push_ctrl_credit #(
      .Depth(Depth),
      .Width(Width),
      .RamWriteLatency(RamWriteLatency),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterResetActive(RegisterResetActive),
      .MaxCredit(MaxCredit),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_push_ctrl_credit (
      .clk              (push_clk),               // ri lint_check_waive SAME_CLOCK_NAME
      // Not using push_either_rst here so that there is no path from
      // push_sender_in_reset to push_receiver_in_reset.
      .rst              (push_rst),
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .full             (push_full),
      .slots            (push_slots),
      .ram_wr_valid     (push_ram_wr_valid),
      .ram_wr_addr      (push_ram_wr_addr),
      .ram_wr_data      (push_ram_wr_data),
      .push_count_gray  (push_push_count_gray),
      .pop_count_gray   (push_pop_count_gray),
      .reset_active_pop (push_reset_active_pop),
      .reset_active_push(push_reset_active_push)
  );

  logic push_either_rst;
  assign push_either_rst = push_rst || push_sender_in_reset;

  br_cdc_fifo_gray_count_sync #(
      .CountWidth(CountWidth),
      .NumStages (NumSyncStages)
  ) br_cdc_fifo_gray_count_sync_pop2push (
      // TODO(zhemao): Remove need for pop_clk and pop_rst here.
      .src_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(pop_rst),
      .src_count_gray(pop_pop_count_gray),
      .dst_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(push_either_rst),
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
      .dst_rst(push_either_rst),
      .dst_bit(push_reset_active_pop)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_cdc_fifo_ctrl_push_1r1w_push_credit
