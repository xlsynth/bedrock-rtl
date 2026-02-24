
// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Shared Dynamic Multi-FIFO Controller
// (Push Valid/Credit Interface, Pop Credit/Valid Interface with external arbiter interface)
//
// This module implements the controller for a shared storage multi-FIFO
// with dynamic allocation.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs dynamically.
// The order of RAM entries for a single logical FIFO is tracked via
// singly-linked lists. The linked lists are stored in a separate
// pointer RAM. The data and pointer RAMs must be instantiated
// externally to this module and connected to the `data_ram_*` and
// `ptr_ram_*` ports.
// The push interface provides a valid/credit interface and a binary-encoded
// FIFO ID. The push data is appended to the logical FIFO with the specified ID.
//
// The FIFO controller supports multiple write ports. Each write port has its own
// push_valid and push_data, but the push_credit return is shared by all push
// ports and returns up to `NumWritePorts` credits every cycle. The sender can
// send on every push_valid flow in the same cycle if it has sufficient credit,
// even if multiple flows are destined for the same logical FIFO.
//
// The pop interface uses credit-based flow control. Each logical FIFO has its
// own credit return and credit count. There will be one pop_valid and pop_data
// for each read port, and any logical FIFO can use any read port. The pop_fifo_id
// will indicate the logical FIFO the data is read from. A logical FIFO can be popped
// as long as it has at least one credit available. The bandwidth of a single logical FIFO
// is bounded by the maximum available credit and the RAM read latency.
// That is, it is `PopMaxCredits / (RamReadLatency + 1)`.
//
// The controller supports multiple read ports. Each logical FIFO can use any of the read ports.
// The mapping of reads to ports is based on the lower bits of the read address. Each logical FIFO can
// only pop at most one item per cycle. Therefore, there must be at least as
// many active logical FIFOs as read ports to fully utilize the read bandwidth.
//
// Because the pop bandwidth of a linked list is limited by the pointer RAM read
// latency, the multi-FIFO supports using multiple linked lists per logical
// FIFO, configured by the `NumLinkedListsPerFifo` parameter. The linked list
// controller will cycle through the linked list heads in round-robin fashion.
// The bandwidth is also limited by the staging buffer depth and data RAM read
// latency. Up to `PopMaxCredits` reads can be inflight to the RAM at any
// time. Thus, the bandwidth of a single logical FIFO is capped at
// the minimum of `NumLinkedListsPerFifo / (PointerRamReadLatency + 1)` and
// `PopMaxCredits / (DataRamReadLatency + 1)`. To get full bandwidth,
// the number of linked lists per FIFO should be set to `PointerRamReadLatency +
// 1` and the maximum number of credits should be set to `DataRamReadLatency + 1`.

// The design assumes that the data and pointer RAMs and are instantiated externally.
//
// This design assumes there are external arbiters deciding the arbitration policy
// for each read port. The arb_request, arb_grant, and arb_enable_priority_update
// signals are used to connect to the external arbiters. The interface is compatible
// to the standard arbiters like br_arb_fixed, br_arb_rr, and br_arb_lru.

`include "br_asserts_internal.svh"

// ri lint_check_waive MOD_NAME
module br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // Number of write ports. Must be >=1.
    parameter int NumWritePorts = 1,
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // The maximum number of pop-side credits that can be available to a single FIFO.
    parameter int PopMaxCredits = 1,
    // The number of sub-linked lists used by each logical FIFO.
    // This affects the pop bandwidth of each logical FIFO.
    // The max bandwidth will be `NumLinkedListsPerFifo / (PointerRamReadLatency + 1)`.
    parameter int NumLinkedListsPerFifo = 1,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int DataRamReadLatency = 0,
    // The number of cycles between pointer ram read address and read data. Must be >=0.
    parameter int PointerRamReadLatency = 0,
    // If 1, add a retiming stage to the push_credit signal so that it is
    // driven directly from a flop. This comes at the expense of one additional
    // cycle of credit loop latency.
    parameter bit RegisterPushOutputs = 0,
    // If 1, cover that push_credit_stall can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushCreditStall = 1,
    // If 1, cover that credit_withhold can be non-zero.
    // Otherwise, assert that it is always zero.
    parameter bit EnableCoverCreditWithhold = 1,
    // If 1, cover that push_sender_in_reset can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushSenderInReset = 1,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int PopCreditWidth = $clog2(PopMaxCredits + 1),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic push_sender_in_reset,
    output logic push_receiver_in_reset,
    input logic push_credit_stall,
    output logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    output logic push_full,
    input logic [CountWidth-1:0] credit_initial_push,
    input logic [CountWidth-1:0] credit_withhold_push,
    output logic [CountWidth-1:0] credit_available_push,
    output logic [CountWidth-1:0] credit_count_push,

    // Pop side
    output logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [NumFifos-1:0] pop_credit,
    output logic [NumReadPorts-1:0] pop_valid,
    output logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    output logic [NumReadPorts-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0] pop_empty,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][PopCreditWidth-1:0] credit_withhold_pop,
    output logic [NumFifos-1:0][PopCreditWidth-1:0] credit_available_pop,
    output logic [NumFifos-1:0][PopCreditWidth-1:0] credit_count_pop,
    // Arbiter interface
    output logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    output logic [NumReadPorts-1:0] arb_enable_priority_update,
    // Data RAM Ports
    output logic [NumWritePorts-1:0] data_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    output logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    output logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // Pointer RAM Ports
    output logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    output logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,

    output logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    output logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data
);

  // Integration Checks
  `BR_ASSERT_STATIC(num_write_ports_in_range_a, NumWritePorts >= 1)
  `BR_ASSERT_STATIC(legal_num_read_ports_a, NumReadPorts >= 1 && br_math::is_power_of_2(
                    NumReadPorts))
  `BR_ASSERT_STATIC(pointer_ram_read_latency_in_range_a, PointerRamReadLatency >= 0)
  `BR_ASSERT_STATIC(data_ram_read_latency_in_range_a, DataRamReadLatency >= 0)
  `BR_ASSERT_STATIC(num_fifos_in_range_a, NumFifos >= 2)
  `BR_ASSERT_STATIC(depth_in_range_a, Depth > 2 * NumWritePorts && Depth >= NumReadPorts)
  `BR_ASSERT_STATIC(width_in_range_a, Width >= 1)

  // Other integration checks in submodules

  // Implementation
  // Push Controller
  logic [NumFifos-1:0][NumWritePorts-1:0] next_tail_valid;
  logic [NumFifos-1:0][NumWritePorts-1:0][AddrWidth-1:0] next_tail;
  logic [NumFifos-1:0] dealloc_valid;
  logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id;
  logic push_ctrl_rst;
  logic ptr_mgr_rst;
  logic pop_ctrl_rst;
  assign push_ctrl_rst = rst || pop_receiver_in_reset;
  assign ptr_mgr_rst   = rst || pop_receiver_in_reset || push_sender_in_reset;
  assign pop_ctrl_rst  = rst || push_sender_in_reset;

  br_fifo_shared_dynamic_push_ctrl_credit #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_push_ctrl_credit_inst (
      .clk,
      .rst(push_ctrl_rst),
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_fifo_id,
      .push_data,
      .push_full,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_available_push,
      .credit_count_push,
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .next_tail_valid,
      .next_tail,
      .dealloc_valid,
      .dealloc_entry_id
  );

  // Pointer Manager
  logic [NumFifos-1:0] ram_empty;
  logic [NumFifos-1:0] head_ready;
  logic [NumFifos-1:0] head_valid;
  logic [NumFifos-1:0][AddrWidth-1:0] head;

  br_fifo_shared_dynamic_ptr_mgr #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumLinkedListsPerFifo(NumLinkedListsPerFifo),
      .RamReadLatency(PointerRamReadLatency)
  ) br_fifo_shared_dynamic_ptr_mgr_inst (
      .clk,
      .rst(ptr_mgr_rst),
      .next_tail_valid,
      .next_tail,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data,
      .head_valid,
      .head_ready,
      .head,
      .empty(ram_empty),
      .items()  // Not used
  );

  // Pop Controller
  br_fifo_shared_pop_ctrl_credit_ext_arbiter #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .PopMaxCredits(PopMaxCredits),
      .RamReadLatency(DataRamReadLatency),
      .RegisterDeallocation(RegisterDeallocation)
  ) br_fifo_shared_pop_ctrl_credit_ext_arbiter_inst (
      .clk,
      .rst(pop_ctrl_rst),
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_valid,
      .pop_fifo_id,
      .pop_data,
      .pop_empty,
      .credit_initial_pop,
      .credit_withhold_pop,
      .credit_available_pop,
      .credit_count_pop,
      .arb_request,
      .arb_grant,
      .arb_can_grant(arb_grant),
      .arb_enable_priority_update,
      .dealloc_valid,
      .dealloc_entry_id,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data
  );

  // Implementation Checks

  // TODO(zhemao): Add the checks
endmodule : br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_ext_arbiter
