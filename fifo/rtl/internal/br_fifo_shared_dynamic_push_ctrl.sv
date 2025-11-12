// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Dynamic Multi-FIFO Push Controller

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_shared_dynamic_push_ctrl #(
    // Number of write ports
    parameter int NumWritePorts = 1,
    // Number of logical FIFOs
    parameter int NumFifos = 2,
    // Total depth of the FIFO
    parameter int Depth = 3,
    // Width of the data
    parameter int Width = 1,
    // The delay between an entry being deallocated and when the deallocation
    // is indicated by dealloc_count.
    parameter int DeallocCountDelay = 2,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth),
    localparam int FifoCountWidth = $clog2(NumFifos + 1)
) (
    input logic clk,
    input logic rst,

    // Push side
    output logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    output logic push_full,

    // Data RAM write ports
    output logic [NumWritePorts-1:0] data_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    output logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    // To Linked List Controllers
    output logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid,
    output logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail,

    // Entry deallocation from pop controller
    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,
    output logic [FifoCountWidth-1:0] dealloc_count
);

  // Integration Assertions

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS

  logic [NumWritePorts-1:0][Width+FifoIdWidth-1:0] push_comb_data;

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_push_comb_data
    assign push_comb_data[i] = {push_fifo_id[i], push_data[i]};
  end

  br_flow_checks_valid_data_intg #(
      .NumFlows(NumWritePorts),
      .Width(Width + FifoIdWidth),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg_inst (
      .clk,
      .rst,
      .valid(push_valid),
      .ready(push_ready),
      .data (push_comb_data)
  );

  // Push data could be unknown, but fifo_id must always be known.
  // Add the check specifically in case the data check is disabled.
  if (!EnableAssertPushDataKnown) begin : gen_fifo_id_known_check
    for (genvar i = 0; i < NumWritePorts; i++) begin : gen_fifo_id_known_check_port
      `BR_ASSERT_INTG(fifo_id_known_a, push_valid[i] |-> !$isunknown(push_fifo_id[i]))
    end
  end

`endif  // BR_DISABLE_INTG_CHECKS
`endif  // BR_ASSERT_ON

  // Implementation
  localparam int AllocCountWidth = $clog2(NumWritePorts + 1);

  logic [AllocCountWidth-1:0] alloc_sendable;
  logic [AllocCountWidth-1:0] alloc_receivable;
  logic [NumWritePorts-1:0][AddrWidth-1:0] alloc_entry_id;

  br_tracker_freelist #(
      .NumEntries(Depth),
      .NumAllocPerCycle(NumWritePorts),
      .NumDeallocPorts(NumFifos),
      .DeallocCountDelay(DeallocCountDelay)
  ) br_tracker_freelist_inst (
      .clk,
      .rst,

      .alloc_sendable,
      .alloc_receivable,
      .alloc_entry_id,

      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_count
  );

  assign push_full = alloc_sendable == '0;

  if (NumWritePorts > 1) begin : gen_alloc_mapping
    // Distribute the allocatable entries to the active push ports using multi-grant
    // round-robin arbitration.
    br_multi_xfer_distributor_rr #(
        .NumSymbols(NumWritePorts),
        .NumFlows(NumWritePorts),
        .SymbolWidth(AddrWidth),
        .EnableCoverMorePopReadyThanSendable(EnableCoverPushBackpressure),
        // TODO(zhemao): check this is right
        .EnableAssertFinalNotSendable(0)
    ) br_multi_xfer_distributor_rr_inst (
        .clk,
        .rst,
        .push_sendable(alloc_sendable),
        .push_receivable(alloc_receivable),
        .push_data(alloc_entry_id),
        // Ready/valid deliberately reversed here
        .pop_ready(push_valid),
        .pop_valid(push_ready),
        .pop_data(data_ram_wr_addr)
    );

    assign data_ram_wr_valid = push_valid & push_ready;
    assign data_ram_wr_data  = push_data;
  end else begin : gen_single_alloc
    assign push_ready = alloc_sendable;
    assign alloc_receivable = push_valid;

    assign data_ram_wr_valid = push_valid & push_ready;
    assign data_ram_wr_addr = alloc_entry_id;
    assign data_ram_wr_data = push_data;
  end

  for (genvar i = 0; i < NumWritePorts; i++) begin : gen_next_tail
    logic [NumFifos-1:0] port_next_tail_valid;
    logic [NumFifos-1:0][AddrWidth-1:0] port_next_tail;

    br_demux_bin #(
        .NumSymbolsOut(NumFifos),
        .SymbolWidth  (AddrWidth)
    ) br_demux_bin_port_next_tail_valid_inst (
        .select(push_fifo_id[i]),
        .in_valid(data_ram_wr_valid[i]),
        .in(data_ram_wr_addr[i]),
        .out_valid(port_next_tail_valid),
        .out(port_next_tail)
    );

    for (genvar j = 0; j < NumFifos; j++) begin : gen_fifo_next_tail
      assign next_tail_valid[j][i] = port_next_tail_valid[j];
      assign next_tail[j][i] = port_next_tail[j];
    end
  end

  // Implementation Checks

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  localparam int PortCountWidth = $clog2(NumWritePorts + 1);

  logic [PortCountWidth-1:0] request_count;
  logic [PortCountWidth-1:0] grant_count;

  // These are only used for assertions, so it's fine to use $countones
  // ri lint_check_off SYS_TF
  assign request_count = $unsigned($countones(push_valid));
  assign grant_count   = $unsigned($countones(push_valid & push_ready));
  // ri lint_check_on SYS_TF
`endif
`endif

  `BR_ASSERT_IMPL(
      full_push_acceptance_a,
      (|push_valid && (alloc_sendable >= request_count)) |-> (request_count == grant_count))
  if (EnableCoverPushBackpressure) begin : gen_partial_push_acceptance_check
    `BR_ASSERT_IMPL(
        partial_push_acceptance_a,
        (|push_valid && (alloc_sendable < request_count)) |-> (grant_count == alloc_sendable))
  end

endmodule
