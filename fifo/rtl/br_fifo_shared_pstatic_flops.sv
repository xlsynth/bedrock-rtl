// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface)
//
// This module implements a shared storage multi-FIFO with pseudo-static allocation
// of storage from a flop-based RAM.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs statically at initialization,
// and a separate set of read/write pointers are kept per logical FIFO.

// For instance, for a 4-FIFO design with a depth of 16, the sizes of the
// logical FIFOs might be [6, 2, 3, 5]. In this case, you would configure
// the base and bound addresses as [(0, 5), (6, 7), (8, 10), (11, 15)] and the
// layout of the flop storage is as follows:
//
//  +----------------------------------------------------------------------------+
//  | Addr | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
//  |------|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|
//  | FIFO | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 2 | 2 | 2  | 3  | 3  | 3  | 3  | 3  |
//  +----------------------------------------------------------------------------+
//
// The push interface provides a valid/ready interface and a binary-encoded
// FIFO ID. The push data is appended to the logical FIFO with the specified ID.
//
// Every logical FIFO has its own ready/valid pop interface. If the data RAM
// read latency is non-zero or the RegisterPopOutputs parameter is set to 1, the
// pop_data will be provided from a staging buffer per logical FIFO. The staging
// buffers are refilled from the data RAM and arbitrate with each other for
// access using a round-robin arbitration scheme. The depth of each staging
// buffer can be configured with the StagingBufferDepth parameter. The
// bandwidth of a single logical FIFO is determined by the staging buffer depth
// and is equivalent to `StagingBufferDepth / (RamReadLatency + 1)`.
//
// The cut-through latency of the FIFO is `1 + RamReadLatency + RegisterPopOutputs`.
// The backpressure latency of the FIFO is 1.
// The maximum bandwidth across all logical FIFOs is `NumFifos * StagingBufferDepth / (RamReadLatency + 1)`.

`include "br_asserts_internal.svh"

module br_fifo_shared_pstatic_flops #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (PointerRamAddressDepthStages
    // + PointerRamReadDataDepthStages + PointerRamReadDataWidthStages + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // Number of tiles in the depth dimension for the flop RAM.
    parameter int RamDepthTiles = 1,
    // Number of tiles in the width dimension for the flop RAM.
    parameter int RamWidthTiles = 1,
    // Number of stages on the address path for the flop RAM.
    parameter int RamAddressDepthStages = 0,
    // Number of stages in the depth dimension on the flop RAM.
    parameter int RamReadDataDepthStages = 0,
    // Number of stages in the width dimension on the flop RAM.
    parameter int RamReadDataWidthStages = 0,
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
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Size configuration
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
    input  logic                   push_valid,
    output logic                   push_ready,
    input  logic [      Width-1:0] push_data,
    input  logic [FifoIdWidth-1:0] push_fifo_id,
    output logic [   NumFifos-1:0] push_full,

    // Pop side
    output logic [NumFifos-1:0]            pop_valid,
    input  logic [NumFifos-1:0]            pop_ready,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0]            pop_empty
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

  br_fifo_shared_pstatic_ctrl #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_ctrl (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_error,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .push_full,
      .pop_valid,
      .pop_ready,
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

endmodule
