
// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO w/ Flop-based Storage
// (Push Valid/Credit Interface, Pop Ready/Valid Interface)
//
// This module implements a shared storage multi-FIFO with flop-based storage.
// and pseudo-static allocation.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs statically at initialization,
// and a separate set of read/write pointers are kept per logical FIFO.
// For instance, for a 4-FIFO design with a depth of 16, the sizes of the
// logical FIFOs might be [6, 2, 3, 5]. In this case, you would configure
// the base and bound addresses as [(0, 5), (6, 7), (8, 10), (11, 15)] and the
// layout of the data RAM is as follows:
//
//  +----------------------------------------------------------------------------+
//  | Addr | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
//  |------|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|
//  | FIFO | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 2 | 2 | 2  | 3  | 3  | 3  | 3  | 3  |
//  +----------------------------------------------------------------------------+
//
// The push interface provides a valid/credit interface and a binary-encoded
// FIFO ID. The push data is appended to the logical FIFO with the specified ID.
//
// Since there is a separate allocation for each logical FIFO, each logical FIFO
// has its own independent credit return.
//
// Every logical FIFO has its own ready/valid pop interface. If the data RAM
// read latency is non-zero or the RegisterPopOutputs parameter is set to 1, the
// pop_data will be provided from a staging buffer per logical FIFO. The staging
// buffers are refilled from the data RAM and arbitrate with each other for
// access. The depth of each staging buffer can be configured with the
// StagingBufferDepth parameter. The bandwidth of a single logical FIFO is
// determined by the staging buffer depth and is equivalent to
// `StagingBufferDepth / (RamReadLatency + 1)`.
//
// The design uses internal flop-based RAMs for the data storage.
// The latency of the internal RAM is determined from the retiming parameters as follows:
//
// `RamReadLatency = RamAddressDepthStages + RamReadDataDepthStages + RamReadDataWidthStages`
//
// The design uses internal arbiters to determine which logical FIFOs can use the RAM read ports
// on a given cycle. The arbitration policy is least-recently used (LRU).

`include "br_asserts_internal.svh"

// ri lint_check_waive MOD_NAME
module br_fifo_shared_pstatic_flops_push_credit #(
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
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The max bandwidth will be `StagingBufferDepth / (DataRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // Number of tiles in the depth dimension for the data flop RAM.
    parameter int RamDepthTiles = 1,
    // Number of tiles in the width dimension for the data flop RAM.
    parameter int RamWidthTiles = 1,
    // Number of stages on the address path for the data flop RAM.
    parameter int RamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the data flop RAM.
    parameter int RamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the data flop RAM.
    parameter int RamReadDataWidthStages = 0,
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
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,
    // Fifo configuration
    // These can come from straps or CSRs, but they must be set before reset is
    // deasserted and then held stable until reset is asserted.
    // The base and bound addresses determine the range of RAM addresses given
    // to each logical FIFO. They are both inclusive, so logical FIFO i will
    // increment from config_base[i] up to config_bound[i] before wrapping back
    // around to config_base[i] again.
    // The minimum size for a given logical FIFO is 1, meaning that
    // config_bound[i] must be >= config_base[i] for all i.
    // The address ranges must be in ascending order.
    input logic [NumFifos-1:0][AddrWidth-1:0] config_base,
    input logic [NumFifos-1:0][AddrWidth-1:0] config_bound,
    // Error is asserted if the base and bound addresses are misconfigured.
    // For instance, if any address is >= Depth, config_base[i] > config_bound[i],
    // or config_base[i] <= config_bound[i-1] for i > 0.
    output logic config_error,

    // Push side
    input logic push_sender_in_reset,
    output logic push_receiver_in_reset,
    input logic [NumFifos-1:0] push_credit_stall,
    output logic [NumFifos-1:0][PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    output logic [NumFifos-1:0] push_full,
    input logic [NumFifos-1:0][CountWidth-1:0] credit_initial_push,
    input logic [NumFifos-1:0][CountWidth-1:0] credit_withhold_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_available_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_count_push,

    // Pop side
    output logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0] pop_empty
);

  // Integration Checks
  // Rely on checks in the submodules

  // Implementation
  // Data RAM
  logic ram_wr_valid;
  logic [AddrWidth-1:0] ram_wr_addr;
  logic [Width-1:0] ram_wr_data;

  logic ram_rd_addr_valid;
  logic [AddrWidth-1:0] ram_rd_addr;
  logic ram_rd_data_valid;
  logic [Width-1:0] ram_rd_data;

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(1),
      .NumReadPorts(1),
      .DepthTiles(RamDepthTiles),
      .WidthTiles(RamWidthTiles),
      .AddressDepthStages(RamAddressDepthStages),
      .ReadDataDepthStages(RamReadDataDepthStages),
      .ReadDataWidthStages(RamReadDataWidthStages)
  ) br_ram_flops_data (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(ram_wr_valid),
      .wr_addr(ram_wr_addr),
      .wr_data(ram_wr_data),
      .wr_word_en({RamWidthTiles{1'b1}}),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(ram_rd_addr_valid),
      .rd_addr(ram_rd_addr),
      .rd_data_valid(ram_rd_data_valid),
      .rd_data(ram_rd_data)
  );

  // Controller
  localparam int RamReadLatency =
      RamAddressDepthStages + RamReadDataDepthStages + RamReadDataWidthStages;

  br_fifo_shared_pstatic_ctrl_push_credit #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .RegisterDeallocation(RegisterDeallocation),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_ctrl_push_credit_inst (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
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
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data
  );

  // Implementation Checks

  // Rely on implementation checks in the controller
endmodule : br_fifo_shared_pstatic_flops_push_credit
