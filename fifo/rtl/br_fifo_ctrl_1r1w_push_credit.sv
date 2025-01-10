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

// Bedrock-RTL FIFO Controller (1R1W, Push Credit/Valid, Pop Ready/Valid Variant)
//
// A one-read/one-write (1R1W) FIFO controller that uses a credit-valid
// push interface and an AMBA-inspired ready-valid pop interface
// for synchronizing pipeline stages and stalling
// when encountering backpressure hazards.
//
// This module does not include any internal RAM. Instead, it exposes
// read and write ports to an external 1R1W (pseudo-dual-port)
// RAM module, which could be implemented in flops or SRAM.
//
// The FIFO controller can work with RAMs of arbitrary fixed read latency.
// If the latency is non-zero, a FLOP-based staging buffer is kept in the
// controller so that a synchronous ready/valid interface can be maintained
// at the pop interface.
//
// The FIFO can be parameterized in bypass mode or non-bypass mode. In bypass
// mode (default), pushes forward directly to the pop interface or staging
// buffer when the FIFO has fewer than (RamReadLatency + 1) items, allowing the
// FIFO to achieve a cut-through latency of zero cycles. This comes at the
// cost of a combinational timing path from the push interface to the pop
// interface. Conversely, when bypass is disabled, then pushes always go
// through the RAM before they can become visible at the pop interface. This
// results in a cut-through latency of 1 + RamReadLatency cycles, but improves
// static timing by eliminating any combinational paths from push to pop.
//
// The RegisterPopOutputs parameter can be set to 1 to add an additional br_flow_reg_fwd
// before the pop interface of the FIFO. This may improve timing of paths dependent on
// the pop interface at the expense of an additional cycle of cut-through latency.
//
// Bypass is enabled by default to minimize latency accumulation throughout a design.
// It is recommended to disable the bypass only when necessary to close timing.
//
// The RAM interface is required to have a write latency of 1 cycle and a read latency
// of 0 cycles.

`include "br_asserts_internal.svh"

module br_fifo_ctrl_1r1w_push_credit #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then bypasses push-to-pop when the FIFO is empty, resulting in
    // a cut-through latency of 0 cycles, but at the cost of worse timing.
    // If 0, then pushes always go through the RAM before they can become
    // visible at the pop interface. This results in a cut-through latency of
    // 1 cycle, but timing is improved.
    parameter bit EnableBypass = 1,
    // Maximum credit for the internal credit counter. Must be at least Depth.
    // Recommended to not override the default because it is the smallest viable size.
    // Overriding may be convenient if having a consistent credit counter register width
    // (say, 16-bit) throughout a design is deemed useful.
    parameter int MaxCredit = Depth,
    // If 1, add a retiming stage to the push_credit signal so that it is
    // driven directly from a flop. This comes at the expense of one additional
    // cycle of credit loop latency.
    parameter bit RegisterPushCredit = 0,
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional cycle of cut-through latency.
    // If 0, pop_valid/pop_data comes directly from push_valid (if bypass is enabled)
    // and/or ram_wr_data.
    parameter bit RegisterPopOutputs = 1,
    // The number of cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface
    input  logic             push_credit_stall,
    output logic             push_credit,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Pop-side interface
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    output logic                  empty,
    output logic                  empty_next,
    output logic [CountWidth-1:0] items,
    output logic [CountWidth-1:0] items_next,

    // Push-side credits
    input  logic [CreditWidth-1:0] credit_initial_push,
    input  logic [CreditWidth-1:0] credit_withhold_push,
    output logic [CreditWidth-1:0] credit_count_push,
    output logic [CreditWidth-1:0] credit_available_push,

    // 1R1W RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    input  logic                 ram_rd_data_valid,
    input  logic [    Width-1:0] ram_rd_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic bypass_ready;
  logic bypass_valid_unstable;
  logic [Width-1:0] bypass_data_unstable;

  logic push_beat;
  logic pop_beat;

  br_fifo_push_ctrl_credit #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .MaxCredit(MaxCredit),
      .RegisterPushCredit(RegisterPushCredit),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_push_ctrl_credit (
      .clk,
      .rst,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .bypass_ready,
      // Bypass is only used when EnableBypass is 1.
      .bypass_valid_unstable,  // ri lint_check_waive CONST_ASSIGN
      .bypass_data_unstable,  // ri lint_check_waive CONST_ASSIGN
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .push_beat,
      .pop_beat
  );

  br_fifo_pop_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_pop_ctrl (
      .clk,
      .rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .empty_next,
      .items,
      .items_next,
      // Bypass is only used when EnableBypass is 1.
      .bypass_ready,  // ri lint_check_waive CONST_ASSIGN
      .bypass_valid_unstable,
      .bypass_data_unstable,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data,
      .push_beat,
      .pop_beat
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  // TODO(mgottscho): write some

endmodule : br_fifo_ctrl_1r1w_push_credit
