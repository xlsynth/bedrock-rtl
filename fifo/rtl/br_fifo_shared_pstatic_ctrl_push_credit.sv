// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Shared Pseudo-Static Multi-FIFO Controller (Push Valid/Credit Interface)
//
// This module implements the controller for a shared storage multi-FIFO
// with pseudo-static allocation.
//
// The multi-FIFO contains multiple logical FIFOs. Space in the shared
// data RAM is allocated to the logical FIFOs statically at initialization,
// and a separate set of read/write pointers are kept per logical FIFO.
//
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
// Since there is a separate allocation for each logical FIFO, each logical FIFO
// has its own independent credit return.
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
// The backpressure latency of the FIFO is `RegisterPushOutputs`.
// The maximum bandwidth across all logical FIFOs is `NumFifos * StagingBufferDepth / (RamReadLatency + 1)`.

`include "br_asserts_internal.svh"

module br_fifo_shared_pstatic_ctrl_push_credit #(
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than or equal to the number of logical FIFOs.
    parameter int Depth = 2,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // If 1, register is added on the credit returns,
    // improving timing at the cost of additional latency.
    parameter bit RegisterPushOutputs = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The bandwidth will be `StagingBufferDepth / (PointerRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // The number of cycles between ram read address and read data. Must be >=0.
    parameter int RamReadLatency = 0,
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

    // Push-side interface
    input  logic                   push_sender_in_reset,
    output logic                   push_receiver_in_reset,
    input  logic [   NumFifos-1:0] push_credit_stall,
    output logic [   NumFifos-1:0] push_credit,
    input  logic                   push_valid,
    input  logic [      Width-1:0] push_data,
    input  logic [FifoIdWidth-1:0] push_fifo_id,
    output logic [   NumFifos-1:0] push_full,

    input  logic [NumFifos-1:0][CountWidth-1:0] credit_initial_push,
    input  logic [NumFifos-1:0][CountWidth-1:0] credit_withhold_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_available_push,
    output logic [NumFifos-1:0][CountWidth-1:0] credit_count_push,

    // Pop-side interface
    input  logic [NumFifos-1:0]            pop_ready,
    output logic [NumFifos-1:0]            pop_valid,
    output logic [NumFifos-1:0][Width-1:0] pop_data,
    output logic [NumFifos-1:0]            pop_empty,

    // RAM read/write ports
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,
    output logic                 ram_rd_addr_valid,
    output logic [AddrWidth-1:0] ram_rd_addr,
    input  logic                 ram_rd_data_valid,
    input  logic [    Width-1:0] ram_rd_data
);

  // Integration assertions
  `BR_ASSERT_STATIC(num_fifos_gte_2_a, NumFifos >= 2)
  `BR_ASSERT_STATIC(depth_gte_num_fifos_a, Depth >= NumFifos)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)
  // Other integration checks in submodules

  // Implementation
  logic either_rst;

  assign either_rst = push_sender_in_reset || rst;

  logic [NumFifos-1:0][CountWidth-1:0] config_size;

  br_fifo_shared_pstatic_size_calc #(
      .NumFifos(NumFifos),
      .Depth(Depth)
  ) br_fifo_shared_pstatic_size_calc (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_size,
      .config_error
  );

  logic [NumFifos-1:0] advance_tail;
  logic [NumFifos-1:0][AddrWidth-1:0] tail_next;
  logic [NumFifos-1:0][AddrWidth-1:0] tail;
  logic [NumFifos-1:0] dealloc_valid;

  br_fifo_shared_pstatic_push_ctrl_credit #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .RegisterPushOutputs(RegisterPushOutputs),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_push_ctrl (
      .clk,
      .rst,
      .config_base,
      .config_bound,
      .config_size,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .push_data,
      .push_fifo_id,
      .push_full,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_available_push,
      .credit_count_push,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .advance_tail,
      .tail_next,
      .tail,
      .dealloc_valid
  );

  logic [NumFifos-1:0] head_ready;
  logic [NumFifos-1:0] head_valid;
  logic [NumFifos-1:0][AddrWidth-1:0] head;
  logic [NumFifos-1:0] ram_empty;
  logic [NumFifos-1:0][CountWidth-1:0] ram_items;

  br_fifo_shared_pstatic_ptr_mgr #(
      .NumFifos(NumFifos),
      .Depth(Depth),
      // Keep this at 0 for now to avoid introducing extra registers.
      // May expose this as a top-level parameter if there is a timing issue.
      .RegisterRamItems(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_shared_pstatic_ptr_mgr (
      .clk,
      .rst(either_rst),
      .config_base,
      .config_bound,
      .config_size,
      .advance_tail,
      .tail_next,
      .tail,
      .push_full,
      .head_ready,
      .head_valid,
      .head,
      .ram_empty,
      .ram_items
  );

  br_fifo_shared_pop_ctrl #(
      .NumReadPorts(1),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency)
  ) br_fifo_shared_pop_ctrl (
      .clk,
      .rst(either_rst),
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .ram_items,
      .pop_valid,
      .pop_ready,
      .pop_data,
      .pop_empty,
      .dealloc_valid,
      .dealloc_entry_id(),  // Not used
      .data_ram_rd_addr_valid(ram_rd_addr_valid),
      .data_ram_rd_addr(ram_rd_addr),
      .data_ram_rd_data_valid(ram_rd_data_valid),
      .data_ram_rd_data(ram_rd_data)
  );
endmodule
