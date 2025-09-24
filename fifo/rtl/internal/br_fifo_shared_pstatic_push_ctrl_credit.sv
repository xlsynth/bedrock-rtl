// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Push Controller
//
// This module implements the push-side of a pseudo-static multi-FIFO
// with credit-based push interface.
// It tracks NumFifos write pointers that wrap around in dedicated ranges.
// TODO(zhemao): Support for multiple write ports.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_pstatic_push_ctrl_credit #(
    // Number of logical FIFOs
    parameter int NumFifos = 2,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // If 1, register is added on the credit returns,
    // improving timing at the cost of additional latency.
    parameter bit RegisterPushOutputs = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth),
    localparam int CountWidth  = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    // Configuration
    input logic [NumFifos-1:0][CountWidth-1:0] config_size,
    input logic [NumFifos-1:0][ AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][ AddrWidth-1:0] config_bound,

    // Push side
    input logic push_sender_in_reset,
    output logic push_receiver_in_reset,
    input logic [NumFifos-1:0] push_credit_stall,
    output logic [NumFifos-1:0] push_credit,

    input logic push_valid,
    input logic [Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [NumFifos-1:0] push_full,

    input  logic [NumFifos-1:0][CountWidth-1:0] credit_initial_push,
    input  logic [NumFifos-1:0][CountWidth-1:0] credit_withhold_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_available_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_count_push,

    // Data RAM write ports
    output logic ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [Width-1:0] ram_wr_data,

    // Write pointer to pointer manager
    output logic [NumFifos-1:0] advance_tail,
    output logic [NumFifos-1:0][AddrWidth-1:0] tail_next,
    output logic [NumFifos-1:0][AddrWidth-1:0] tail,

    // Entry deallocation from pop controller
    input logic [NumFifos-1:0] dealloc_valid
);
  // Integration Assertions
  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_intg_checks
    `BR_ASSERT_INTG(credit_initial_lte_size_a,
                    $fell(rst) |-> $past(credit_initial_push[i]) <= config_size[i])
    `BR_ASSERT_INTG(credit_withhold_lt_size_a, credit_withhold_push[i] <= config_size[i])
  end
  `BR_UNUSED(config_size)  // Only used for assertions

  // Implementation

  logic either_rst;
  assign either_rst = push_sender_in_reset || rst;

  // Credit Receiver

  logic [NumFifos-1:0] push_receiver_in_reset_internal;
  logic [NumFifos-1:0] receiver_push_valid;

  // We only need to send back one receiver in reset signal.
  // They should all be identical.
  assign push_receiver_in_reset = push_receiver_in_reset_internal[0];
  `BR_UNUSED_NAMED(push_receiver_in_reset_internal_msbs,
                   push_receiver_in_reset_internal[NumFifos-1:1])

  for (genvar i = 0; i < NumFifos; i++) begin : gen_credit_receiver
    // This is just used to track occupancy for assertion purposes.
    assign receiver_push_valid[i] = push_valid && (push_fifo_id == i);

    br_credit_receiver #(
        .NumFlows(1),
        .Width(Width),
        .MaxCredit(Depth),
        .RegisterPushOutputs(RegisterPushOutputs),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        // Each FIFO must have at least one entry assigned to it,
        // so the actual number of credits available to each is
        // Depth - (NumFifos - 1).
        .CoverMaxCredit(Depth - (NumFifos - 1))
    ) br_credit_receiver_inst (
        .clk,
        .rst,
        .push_sender_in_reset,
        .push_receiver_in_reset(push_receiver_in_reset_internal[i]),
        .push_credit_stall(push_credit_stall[i]),
        .push_credit(push_credit[i]),
        .push_valid(receiver_push_valid[i]),
        .push_data,
        .pop_credit(dealloc_valid[i]),
        // These aren't actually used.
        // They're identical to the push valid/data.
        .pop_valid(),
        .pop_data(),
        .credit_initial(credit_initial_push[i]),
        .credit_withhold(credit_withhold_push[i]),
        .credit_available(credit_available_push[i]),
        .credit_count(credit_count_push[i])
    );
  end

  br_fifo_shared_pstatic_push_ctrl #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      // Credit tracking should ensure there's no backpressure here.
      .EnableCoverPushBackpressure(0),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_push_ctrl_inst (
      .clk,
      .rst(either_rst),
      .config_base,
      .config_bound,
      .push_ready(),
      .push_valid,
      .push_data,
      .push_fifo_id,
      .push_full,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .advance_tail,
      .tail_next,
      .tail
  );

  // Implementation Assertions
  for (genvar i = 0; i < NumFifos; i++) begin : gen_per_fifo_impl_checks
    `BR_ASSERT_IMPL(credit_count_lte_size_a, credit_count_push[i] <= config_size[i])
    `BR_ASSERT_IMPL(credit_available_lte_size_a, credit_available_push[i] <= config_size[i])
  end

endmodule
