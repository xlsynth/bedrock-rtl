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

// Bedrock-RTL CDC FIFO Controller (1R1W, Push Ready/Valid, Pop Credit/Valid Variant)
//
// A one-read/one-write (1R1W) asynchronous FIFO controller that uses a
// credit-valid push interface and an AMBA-inspired ready-valid pop interface
// for synchronizing pipeline stages and stalling when encountering backpressure hazards.
//
// This module does not include any internal RAM. Instead, it exposes
// read and write ports to an external 1R1W (pseudo-dual-port)
// RAM module, which could be implemented in flops or SRAM.
//
// Data progresses from one stage to another when both
// the corresponding ready signal and valid signal are
// both 1 on the same cycle. Otherwise, the stage is stalled.
//
// The FIFO controller can work with RAMs of arbitrary fixed read latency.
// If the latency is non-zero, a FLOP-based staging buffer is kept in the
// controller so that a synchronous ready/valid interface can be maintained
// at the pop interface.
//
// The RegisterPopOutputs parameter can be set to 1 to add an additional br_flow_reg_fwd
// before the pop interface of the FIFO. This may improve timing of paths dependent on
// the pop interface at the expense of an additional pop cycle of cut-through latency.

// The cut-through latency (push_valid to pop_valid latency) and backpressure
// latency (pop_ready to push_ready) can be calculated as follows:
//
// Let PushT and PopT be the push period and pop period, respectively.
//
// The cut-through latency is max(RegisterResetActive + 1, RamWriteLatency)
// * PushT + (NumSyncStages + RamReadLatency + RegisterPopOutputs) * PopT.
//
// The backpressure latency is (RegisterResetActive + 1) * PopT + (NumSyncStages
// + RegisterPushOutputs) * PushT.
//
// To achieve full bandwidth, the depth of the FIFO must be at least
// (CutThroughLatency + BackpressureLatency) / max(PushT, PopT).

`include "br_asserts_internal.svh"
`include "br_gates.svh"

module br_cdc_fifo_ctrl_1r1w_push_credit #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data can come directly from the push interface
    // (if bypass is enabled), the RAM read interface, and/or an internal staging
    // buffer (if RAM read latency is >0).
    parameter bit RegisterPopOutputs = 0,
    // The number of push cycles after ram_wr_valid is asserted at which
    // it is safe to read the newly written data.
    parameter int RamWriteLatency = 1,
    // The number of pop cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
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
    // If 1 (the default), register push_rst on push_clk and pop_rst on pop_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless push_rst and pop_rst are driven directly by
    // registers. If set to 0, push_sender_in_reset must be tied to 0.
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

    // Pop-side interface
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Pop-side status flags
    output logic                  pop_empty,
    output logic [CountWidth-1:0] pop_items,

    // Pop-side RAM read interface
    output logic                 pop_ram_rd_addr_valid,
    output logic [AddrWidth-1:0] pop_ram_rd_addr,
    input  logic                 pop_ram_rd_data_valid,
    input  logic [    Width-1:0] pop_ram_rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [CountWidth-1:0] push_push_count_gray;
  logic [CountWidth-1:0] pop_pop_count_gray;
  logic                  push_reset_active_push;
  logic                  pop_reset_active_pop;

  br_cdc_fifo_ctrl_push_1r1w_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .RamWriteLatency(RamWriteLatency),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterResetActive(RegisterResetActive),
      .MaxCredit(MaxCredit),
      .NumSyncStages(NumSyncStages),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_ctrl_push_1r1w_push_credit_inst (
      .push_clk,
      // Not using push_either_rst here so that there is no path from
      // push_sender_in_reset to push_receiver_in_reset.
      .push_rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .push_full,
      .push_slots,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .push_ram_wr_valid,
      .push_ram_wr_addr,
      .push_ram_wr_data,
      .pop_clk,
      .pop_rst,
      .pop_reset_active_pop,
      .pop_pop_count_gray,
      .push_push_count_gray,
      .push_reset_active_push
  );

  logic push_either_rst;
  assign push_either_rst = push_rst || push_sender_in_reset;

  br_cdc_fifo_ctrl_pop_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_ctrl_pop_1r1w_inst (
      .push_clk,
      .push_rst(push_either_rst),
      .pop_reset_active_pop,
      .pop_pop_count_gray,
      .push_push_count_gray,
      .push_reset_active_push,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty,
      .pop_items,
      .pop_ram_rd_addr_valid,
      .pop_ram_rd_addr,
      .pop_ram_rd_data_valid,
      .pop_ram_rd_data
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_cdc_fifo_ctrl_1r1w_push_credit
