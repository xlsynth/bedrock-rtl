// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Multi-FIFO Pop Controller with external arbiter interface
// and credit-based flow control.
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
// The design assumes that the RAM and pointer management are handled externally.
//
// This is identical to br_fifo_shared_pop_ctrl_credit, but with an external
// arbiter interface so that an arbitrary arbitration policy can be chosen for
// the pop side of the FIFO (where NumReadPorts < NumFifos).

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

// ri lint_check_waive MOD_NAME
module br_fifo_shared_pop_ctrl_credit_ext_arbiter #(
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
    // Set to 1 if the arbiter is guaranteed to grant in a cycle when any request is asserted.
    parameter bit ArbiterAlwaysGrants = 1,

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

    output logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [NumFifos-1:0] pop_credit,
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
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // External arbiter interface
    output logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_can_grant,
    output logic [NumReadPorts-1:0] arb_enable_priority_update
);

  // Integration Checks

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumFifos),
      .Width(AddrWidth)
  ) br_flow_checks_valid_data_intg_head (
      .clk,
      .rst,
      .valid(head_valid),
      .ready(head_ready),
      .data (head)
  );

  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_intg_checks
    `BR_ASSERT_INTG(no_head_valid_on_empty_a, ram_empty[i] |-> !head_valid[i])
  end

  // Implementation

  // Reset handling
  logic either_rst;

  // Make sure all state resets if receiver is in reset
  assign either_rst = pop_receiver_in_reset || rst;
  assign pop_sender_in_reset = rst;

  // Credit counters

  logic [NumFifos-1:0] fifo_ram_rd_addr_valid;
  logic [NumFifos-1:0] fifo_ram_rd_addr_ready;
  logic [NumFifos-1:0][AddrWidth-1:0] fifo_ram_rd_addr;

  for (genvar i = 0; i < NumFifos; i++) begin : gen_fifo_ram_read
    logic ram_rd_req_valid;
    logic ram_rd_req_ready;

    br_credit_counter #(
        .MaxValue(PopMaxCredits)
    ) br_credit_counter (
        .clk,
        .rst(either_rst),
        .incr_valid(pop_credit[i]),
        .incr(1'b1),
        // These are in fact reversed on purpose
        // `decr_ready` indicates when there is credit available to decrement
        // `decr_valid` indicates that the credit should be decremented
        .decr_ready(ram_rd_req_valid),
        .decr_valid(ram_rd_req_ready),
        .decr(1'b1),
        .initial_value(credit_initial_pop[i]),
        .withhold(credit_withhold_pop[i]),
        .value(credit_count_pop[i]),
        .available(credit_available_pop[i])
    );

    br_flow_join #(
        .NumFlows(2)
    ) br_flow_join_ram_rd_addr (
        .clk,
        .rst(either_rst),

        .push_valid({head_valid[i], ram_rd_req_valid}),
        .push_ready({head_ready[i], ram_rd_req_ready}),
        .pop_valid (fifo_ram_rd_addr_valid[i]),
        .pop_ready (fifo_ram_rd_addr_ready[i])
    );

    assign pop_empty[i] = ram_empty[i];
    assign fifo_ram_rd_addr[i] = head[i];
  end

  // Read Crossbar
  // TODO(zhemao): Support an option to have dedicated read ports for a FIFO
  // or group of FIFOs instead of spreading reads across all read ports.
  br_fifo_shared_read_xbar #(
      .NumFifos(NumFifos),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(RamReadLatency),
      .EnableAssertPushValidStability(1),
      .ArbiterAlwaysGrants(ArbiterAlwaysGrants)
  ) br_fifo_shared_read_xbar (
      .clk,
      .rst(either_rst),

      .push_rd_addr_valid(fifo_ram_rd_addr_valid),
      .push_rd_addr_ready(fifo_ram_rd_addr_ready),
      .push_rd_addr(fifo_ram_rd_addr),
      .push_rd_data_valid(),
      .push_rd_data(),

      .pop_rd_addr_valid(data_ram_rd_addr_valid),
      .pop_rd_addr(data_ram_rd_addr),
      .pop_rd_data_valid(data_ram_rd_data_valid),
      .pop_rd_data(data_ram_rd_data),

      .arb_request,
      .arb_can_grant,
      .arb_grant,
      .arb_enable_priority_update
  );

  // Pop FIFO ID encoding and delay
  for (genvar i = 0; i < NumReadPorts; i++) begin : gen_pop_fifo_id_onehot
    logic pop_fifo_id_valid;
    logic [FifoIdWidth-1:0] ram_rd_fifo_id;

    br_enc_onehot2bin #(
        .NumValues(NumFifos)
    ) br_enc_onehot2bin_ram_rd_fifo_id (
        .clk,
        .rst(either_rst),
        .in(arb_grant[i]),
        .out_valid(),
        .out(ram_rd_fifo_id)
    );

    br_delay_valid #(
        .NumStages(RamReadLatency),
        .Width(FifoIdWidth)
    ) br_delay_valid_pop_fifo_id (
        .clk,
        .rst(either_rst),
        .in_valid(data_ram_rd_addr_valid[i]),
        .in(ram_rd_fifo_id),
        .out_valid(pop_fifo_id_valid),
        .out(pop_fifo_id[i]),
        .out_valid_stages(),
        .out_stages()
    );

    assign pop_valid[i] = data_ram_rd_data_valid[i];
    assign pop_data[i]  = data_ram_rd_data[i];

    `BR_UNUSED(pop_fifo_id_valid)  // Used for assertion only

    `BR_ASSERT_IMPL(expected_read_latency_a, pop_fifo_id_valid |-> data_ram_rd_data_valid[i])
  end

  // Optional deallocation registers
  if (RegisterDeallocation) begin : gen_reg_dealloc
    logic [NumFifos-1:0] dealloc_valid_next;

    assign dealloc_valid_next = head_valid & head_ready;
    `BR_REGX(dealloc_valid, dealloc_valid_next, clk, either_rst)

    for (genvar i = 0; i < NumFifos; i++) begin : gen_reg_dealloc_entry_id
      `BR_REGLX(dealloc_entry_id[i], head[i], dealloc_valid_next[i], clk, either_rst)
    end
  end else begin : gen_no_reg_dealloc
    assign dealloc_valid = head_valid & head_ready;
    assign dealloc_entry_id = head;
  end

endmodule
