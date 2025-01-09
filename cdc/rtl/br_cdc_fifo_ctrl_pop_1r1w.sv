// Copyright 2024 The Bedrock-RTL Authors
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

// Pop-side of Bedrock-RTL CDC FIFO Controller (1R1W, Ready/Valid Variant)
//
// The pop side of a one-read/one-write (1R1W) asynchronous FIFO controller
// that uses the AMBA-inspired ready-valid handshake protocol for synchronizing
// pipeline stages and stalling when encountering backpressure hazards.
//
// This module does not include any internal RAM. Instead, it exposes
// read ports to an external 1R1W (pseudo-dual-port) RAM module, which
// could be implemented in flops or SRAM.
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
// The cut-through latency is max(2, RamWriteLatency + 1) * PushT +
// (NumSyncStages + 1 + RamReadLatency + RegisterPopOutputs) * PopT.

// The backpressure latency is 2 * PopT + (NumSyncStages + 1) * PushT.
//
// To achieve full bandwidth, the depth of the FIFO must be at least
// (CutThroughLatency + BackpressureLatency) / max(PushT, PopT).

`include "br_asserts_internal.svh"
`include "br_gates.svh"

module br_cdc_fifo_ctrl_pop_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data can come directly from the push interface
    // (if bypass is enabled), the RAM read interface, and/or an internal staging
    // buffer (if RAM read latency is >0).
    parameter bit RegisterPopOutputs = 0,
    // The number of pop cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
    // The number of synchronization stages to use for the gray counts.
    parameter int NumSyncStages = 3,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Signals that connect to the push side.
    output logic                  pop_reset_active_pop,
    output logic [CountWidth-1:0] pop_pop_count_gray,
    input  logic [CountWidth-1:0] push_push_count_gray,
    input  logic                  push_reset_active_push,

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
    output logic                  pop_empty_next,
    output logic [CountWidth-1:0] pop_items,
    output logic [CountWidth-1:0] pop_items_next,

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

  logic [CountWidth-1:0] pop_push_count_gray;
  logic                  pop_reset_active_push;
  logic [     Width-1:0] pop_ram_rd_data_maxdel;

  br_cdc_fifo_gray_count_sync #(
      .CountWidth(CountWidth),
      .NumStages (NumSyncStages)
  ) br_cdc_fifo_gray_count_sync_push2pop (
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(push_rst),
      .src_count_gray(push_push_count_gray),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(pop_rst),
      .dst_count_gray(pop_push_count_gray)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_reset_active_push (
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(push_rst),
      .src_bit(push_reset_active_push),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(pop_rst),
      .dst_bit(pop_reset_active_push)
  );

  br_cdc_fifo_pop_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency)
  ) br_cdc_fifo_pop_ctrl (
      .clk              (pop_clk),                 // ri lint_check_waive SAME_CLOCK_NAME
      .rst              (pop_rst),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty            (pop_empty),
      .empty_next       (pop_empty_next),
      .items            (pop_items),
      .items_next       (pop_items_next),
      .ram_rd_addr_valid(pop_ram_rd_addr_valid),
      .ram_rd_addr      (pop_ram_rd_addr),
      .ram_rd_data_valid(pop_ram_rd_data_valid),
      .ram_rd_data      (pop_ram_rd_data_maxdel),
      .push_count_gray  (pop_push_count_gray),
      .pop_count_gray   (pop_pop_count_gray),
      .reset_active_pop (pop_reset_active_pop),
      .reset_active_push(pop_reset_active_push)
  );

  // Tag this signal as needing max delay checks
  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL_BUS(pop_ram_rd_data_maxdel, pop_ram_rd_data, Width)
  // ri lint_check_on ONE_CONN_PER_LINE

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(no_pop_valid_when_empty_a, pop_empty |-> !pop_valid, pop_clk, pop_rst)

endmodule : br_cdc_fifo_ctrl_pop_1r1w
