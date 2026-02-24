
// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Shared Dynamic Multi-FIFO with Flop-based Storage
// (Push Valid/Credit Interface, Pop Credit/Valid Interface)
//
// This module implements a shared storage multi-FIFO with flop-based storage
// and dynamic allocation.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs dynamically.
// The order of RAM entries for a single logical FIFO is tracked via
// singly-linked lists. The linked lists are stored in a separate
// pointer RAM.
// The data and pointer RAMs are implemented as flops and instantiated
// internally.
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
//
// The design uses internal flop-based RAMs for the data and pointer storage.
// The latency of the internal RAMs are determined from the retiming parameters as follows:
//
// `PointerRamReadLatency = PointerRamAddressDepthStages + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages`
//
// `DataRamReadLatency = DataRamReadAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages`
//
//
// The design uses internal arbiters to determine which logical FIFOs can use the RAM read ports
// on a given cycle. The arbitration policy is least-recently used (LRU).

`include "br_asserts_internal.svh"

// ri lint_check_waive MOD_NAME
module br_fifo_shared_dynamic_flops_push_credit_pop_credit #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports and at least the number of read ports.
    parameter int Depth = 3,
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
    // Number of tiles in the depth dimension for the data flop RAM.
    parameter int DataRamDepthTiles = 1,
    // Number of tiles in the width dimension for the data flop RAM.
    parameter int DataRamWidthTiles = 1,
    // Number of stages on the address path for the data flop RAM.
    parameter int DataRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the data flop RAM.
    parameter int DataRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the data flop RAM.
    parameter int DataRamReadDataWidthStages = 0,
    // Number of tiles in the depth dimension for the pointer flop RAM.
    parameter int PointerRamDepthTiles = 1,
    // Number of tiles in the width dimension for the pointer flop RAM.
    parameter int PointerRamWidthTiles = 1,
    // Number of stages on the address path for the pointer flop RAM.
    parameter int PointerRamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the pointer flop RAM.
    parameter int PointerRamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the pointer flop RAM.
    parameter int PointerRamReadDataWidthStages = 0,
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
    output logic [NumFifos-1:0][PopCreditWidth-1:0] credit_count_pop
);

  // Integration Checks
  // Rely on checks in the submodules

  // Implementation
  logic any_rst;
  assign any_rst = rst || push_sender_in_reset || pop_receiver_in_reset;


  // Data RAM
  logic [NumWritePorts-1:0] data_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr;
  logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data;

  logic [NumReadPorts-1:0] data_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr;
  logic [NumReadPorts-1:0] data_ram_rd_data_valid;
  logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(DataRamDepthTiles),
      .WidthTiles(DataRamWidthTiles),
      .AddressDepthStages(DataRamAddressDepthStages),
      .ReadDataDepthStages(DataRamReadDataDepthStages),
      .ReadDataWidthStages(DataRamReadDataWidthStages)
  ) br_ram_flops_data (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(any_rst),
      .wr_valid(data_ram_wr_valid),
      .wr_addr(data_ram_wr_addr),
      .wr_data(data_ram_wr_data),
      .wr_word_en({(NumWritePorts * DataRamWidthTiles) {1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(any_rst),
      .rd_addr_valid(data_ram_rd_addr_valid),
      .rd_addr(data_ram_rd_addr),
      .rd_data_valid(data_ram_rd_data_valid),
      .rd_data(data_ram_rd_data)
  );

  // Pointer RAM
  logic [NumWritePorts-1:0] ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr;
  logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data;

  logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr;
  logic [NumReadPorts-1:0] ptr_ram_rd_data_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(AddrWidth),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .DepthTiles(PointerRamDepthTiles),
      .WidthTiles(PointerRamWidthTiles),
      .AddressDepthStages(PointerRamAddressDepthStages),
      .ReadDataDepthStages(PointerRamReadDataDepthStages),
      .ReadDataWidthStages(PointerRamReadDataWidthStages)
  ) br_ram_flops_pointer (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(any_rst),
      .wr_valid(ptr_ram_wr_valid),
      .wr_addr(ptr_ram_wr_addr),
      .wr_data(ptr_ram_wr_data),
      .wr_word_en({(NumWritePorts * PointerRamWidthTiles) {1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(any_rst),
      .rd_addr_valid(ptr_ram_rd_addr_valid),
      .rd_addr(ptr_ram_rd_addr),
      .rd_data_valid(ptr_ram_rd_data_valid),
      .rd_data(ptr_ram_rd_data)
  );

  // Controller
  localparam int DataRamReadLatency =
      DataRamAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages;
  localparam int PointerRamReadLatency =
      PointerRamAddressDepthStages + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages;

  br_fifo_shared_dynamic_ctrl_push_credit_pop_credit #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .PopMaxCredits(PopMaxCredits),
      .NumLinkedListsPerFifo(NumLinkedListsPerFifo),
      .DataRamReadLatency(DataRamReadLatency),
      .PointerRamReadLatency(PointerRamReadLatency),
      .RegisterDeallocation(RegisterDeallocation),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_dynamic_ctrl_push_credit_pop_credit_inst (
      .clk,
      .rst,
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
      .data_ram_wr_valid,
      .data_ram_wr_addr,
      .data_ram_wr_data,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  // Implementation Checks

  // Rely on implementation checks in the controller
endmodule : br_fifo_shared_dynamic_flops_push_credit_pop_credit
