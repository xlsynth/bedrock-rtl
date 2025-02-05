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

// Bedrock-RTL CDC FIFO (Internal 1R1W Flop-RAM, Push Credit/Valid, Pop Ready/Valid Variant)
//
// A one-read/one-write (1R1W) asynchronous FIFO controller that uses a credit-valid
// push interface and an AMBA-inspired ready-valid pop interface
// for synchronizing pipeline stages and stalling
// when encountering backpressure hazards.
//
// This module includes an internal flop-RAM.
//
// The RegisterPopOutputs parameter can be set to 1 to add an additional br_flow_reg_fwd
// before the pop interface of the FIFO. This may improve timing of paths dependent on
// the pop interface at the expense of an additional pop cycle of cut-through latency.

// The cut-through latency (push_valid to pop_valid latency) and backpressure
// latency (pop_ready to push_ready) can be calculated as follows:
//
// Let PushT and PopT be the push period and pop period, respectively.
//
// The cut-through latency is max(RegisterResetActive + 1, FlopRamAddressDepthStages + 2) * PushT +
// (NumSyncStages + FlopRamAddressDepthStages + FlopRamReadDataDepthStages +
// FlopRamReadDataWidthStages + RegisterPopOutputs) * PopT.
//
// The backpressure latency is (RegisterResetActive + 1) * PopT +
// (NumSyncStages + RegisterPushOutputs) * PushT.
//
// To achieve full bandwidth, the depth of the FIFO must be at least
// (CutThroughLatency + BackpressureLatency) / max(PushT, PopT).


module br_cdc_fifo_flops_push_credit #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // Maximum credit for the internal credit counter. Must be at least Depth.
    // Recommended to not override the default because it is the smallest viable size.
    // Overriding may be convenient if having a consistent credit counter register width
    // (say, 16-bit) throughout a design is deemed useful.
    parameter int MaxCredit = Depth,
    // If 1, add a retiming stage to the push_credit signal so that it is
    // driven directly from a flop. This comes at the expense of one additional
    // push cycle of credit loop latency.
    parameter bit RegisterPushOutputs = 0,
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data comes directly from push_valid (if bypass is enabled)
    // and/or ram_wr_data.
    parameter bit RegisterPopOutputs = 1,
    // If 1 (the default), register push_rst on push_clk and pop_rst on pop_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless push_rst and pop_rst are driven directly by
    // registers. If set to 0, push_sender_in_reset must be tied to 0.
    parameter bit RegisterResetActive = 1,
    // Number of synchronization stages to use for the gray counts. Must be >=2.
    parameter int NumSyncStages = 3,
    // Number of tiles in the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int FlopRamDepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int FlopRamWidthTiles = 1,
    // Number of pipeline register stages inserted along the write address and read address paths
    // in the depth dimension. Must be at least 0.
    parameter int FlopRamAddressDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the depth dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the width dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataWidthStages = 0,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,

    // Internal computed parameters
    localparam int AddrWidth   = $clog2(Depth),
    localparam int CountWidth  = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // Push-side posedge-triggered clock.
    input logic push_clk,
    // Push-side synchronous active-high reset.
    input logic push_rst,
    // Pop-side posedge-triggered clock.
    input logic pop_clk,
    // Pop-side synchronous active-high reset.
    input logic pop_rst,

    // Push-side interface
    input  logic             push_sender_in_reset,
    output logic             push_receiver_in_reset,
    input  logic             push_credit_stall,
    output logic             push_credit,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Pop-side interface.
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Push-side status flags
    output logic push_full,
    output logic [CountWidth-1:0] push_slots,

    // Push-side credits
    input  logic [CreditWidth-1:0] credit_initial_push,
    input  logic [CreditWidth-1:0] credit_withhold_push,
    output logic [CreditWidth-1:0] credit_count_push,
    output logic [CreditWidth-1:0] credit_available_push,

    // Pop-side status flags
    output logic pop_empty,
    output logic [CountWidth-1:0] pop_items
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic push_ram_wr_valid;
  logic [AddrWidth-1:0] push_ram_wr_addr;
  logic [Width-1:0] push_ram_wr_data;
  logic pop_ram_rd_addr_valid;
  logic [AddrWidth-1:0] pop_ram_rd_addr;
  logic pop_ram_rd_data_valid;
  logic [Width-1:0] pop_ram_rd_data;

  br_cdc_fifo_ctrl_1r1w_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_ctrl_1r1w_push_credit (
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
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .push_full,
      .push_slots,
      .pop_empty,
      .pop_items,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .push_ram_wr_valid,
      .push_ram_wr_addr,
      .push_ram_wr_data,
      .pop_ram_rd_addr_valid,
      .pop_ram_rd_addr,
      .pop_ram_rd_data_valid,
      .pop_ram_rd_data
  );

  logic push_either_rst;
  assign push_either_rst = push_rst || push_sender_in_reset;

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .DepthTiles(FlopRamDepthTiles),
      .WidthTiles(FlopRamWidthTiles),
      .AddressDepthStages(FlopRamAddressDepthStages),
      .ReadDataDepthStages(FlopRamReadDataDepthStages),
      .ReadDataWidthStages(FlopRamReadDataWidthStages),
      // Flops don't need to be reset, since uninitialized cells will never be read
      .EnableMemReset(0),
      // Since there is an asynchronous path on the read,
      // we need to use structured gates for the read mux.
      .UseStructuredGates(1),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_ram_flops (
      .wr_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(push_either_rst),
      .rd_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(pop_rst),
      .wr_valid(push_ram_wr_valid),
      .wr_addr(push_ram_wr_addr),
      .wr_data(push_ram_wr_data),
      .wr_word_en(1'b1),  // no partial write
      .rd_addr_valid(pop_ram_rd_addr_valid),
      .rd_addr(pop_ram_rd_addr),
      .rd_data_valid(pop_ram_rd_data_valid),
      .rd_data(pop_ram_rd_data)
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

endmodule : br_cdc_fifo_flops_push_credit
