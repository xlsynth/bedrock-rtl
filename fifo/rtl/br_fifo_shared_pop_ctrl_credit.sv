// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Multi-FIFO Pop Controller with credit-based flow control.
//
// This module implements the pop-side control logic for a shared multi-FIFO
// with credit-based flow control on the pop interface.
//
// It manages multiple logical FIFOs that share a common storage RAM. Each
// logical FIFO has its own credit return. There is a single valid/data
// interface per read port that is shared by all FIFOs. The binary-encoded FIFO
// ID is provided alongside the data. The module coordinates reading data from
// the shared RAM, keeping track of available credit, and deallocating entries.
//
// The pop bandwidth per FIFO is determined by the maximum available credit and the RAM read
// latency. The module supports pipelined RAM reads.
//
// The module arbitrates RAM read requests among the logical FIFOs, tracks the head
// pointers of each FIFO, and generates deallocation signals when entries are popped.
//

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

// ri lint_check_waive MOD_NAME
module br_fifo_shared_pop_ctrl_credit #(
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=1.
    parameter int NumFifos = 1,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The maximum number of credits that can be available to a single FIFO.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `PopMaxCredits / (RamReadLatency + 1)`.
    parameter int PopMaxCredits = 1,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int RamReadLatency = 0,

    localparam int AddrWidth   = $clog2(Depth),
    localparam int CreditWidth = $clog2(PopMaxCredits + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    output logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,

    output logic                pop_sender_in_reset,
    input  logic                pop_receiver_in_reset,
    input  logic [NumFifos-1:0] pop_credit,

    output logic [NumReadPorts-1:0] pop_valid,
    output logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    output logic [NumReadPorts-1:0][Width-1:0] pop_data,

    output logic [NumFifos-1:0] pop_empty,

    input  logic [NumFifos-1:0][CreditWidth-1:0] credit_initial_pop,
    input  logic [NumFifos-1:0][CreditWidth-1:0] credit_withhold_pop,
    output logic [NumFifos-1:0][CreditWidth-1:0] credit_available_pop,
    output logic [NumFifos-1:0][CreditWidth-1:0] credit_count_pop,

    output logic [NumFifos-1:0] dealloc_valid,
    output logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);

  // Integration Checks

  // Rely on checks in submodules

  // Implementation

  // Reset handling
  logic either_rst;
  // Make sure all state resets if receiver is in reset
  assign either_rst = pop_receiver_in_reset || rst;

  // Core control logic w/o arbiters

  logic [NumReadPorts-1:0][NumFifos-1:0] arb_request;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_can_grant;
  logic [NumReadPorts-1:0] arb_enable_priority_update;

  br_fifo_shared_pop_ctrl_credit_ext_arbiter #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .PopMaxCredits(PopMaxCredits),
      .RegisterDeallocation(RegisterDeallocation),
      .RamReadLatency(RamReadLatency)
  ) br_fifo_shared_pop_ctrl_credit_ext_arbiter (
      .clk,
      .rst,
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_empty,
      .pop_valid,
      .pop_fifo_id,
      .pop_data,
      .credit_initial_pop,
      .credit_withhold_pop,
      .credit_available_pop,
      .credit_count_pop,
      .dealloc_valid,
      .dealloc_entry_id,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .arb_request,
      .arb_grant,
      .arb_can_grant,
      .arb_enable_priority_update
  );

  // Arbiters
  for (genvar i = 0; i < NumReadPorts; i++) begin : gen_arb_lru
    br_arb_lru_internal #(
        .NumRequesters(NumFifos)
    ) br_arb_lru_internal (
        .clk,
        .rst(either_rst),
        .request(arb_request[i]),
        .can_grant(arb_can_grant[i]),
        .grant(arb_grant[i]),
        .enable_priority_update(arb_enable_priority_update[i])
    );
  end

endmodule
