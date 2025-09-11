// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_ctrl_ext_arbiter_fpv_monitor #(
    // Number of write ports. Must be >=1.
    parameter int NumWritePorts = 1,
    // Number of read ports. Must be >=1 and a power of 2.
    parameter int NumReadPorts = 1,
    // Number of logical FIFOs. Must be >=2.
    parameter int NumFifos = 2,
    // Total depth of the FIFO.
    // Must be greater than two times the number of write ports.
    parameter int Depth = 3,
    // Width of the data. Must be >=1.
    parameter int Width = 1,
    // The depth of the pop-side staging buffer.
    // This affects the pop bandwidth of each logical FIFO.
    // The max bandwidth will be `StagingBufferDepth / (DataRamReadLatency + 1)`.
    parameter int StagingBufferDepth = 1,
    // The number of sub-linked lists used by each logical FIFO.
    // This affects the pop bandwidth of each logical FIFO.
    // The max bandwidth will be `NumLinkedListsPerFifo / (PointerRamReadLatency + 1)`.
    parameter int NumLinkedListsPerFifo = 1,
    // If 1, make sure pop_valid/pop_data are registered at the output
    // of the staging buffer. This adds a cycle of cut-through latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, place a register on the deallocation path from the pop-side
    // staging buffer to the freelist. This improves timing at the cost of
    // adding a cycle of backpressure latency.
    parameter bit RegisterDeallocation = 0,
    // The number of cycles between data ram read address and read data. Must be >=0.
    parameter int DataRamReadLatency = 0,
    // The number of cycles between pointer ram read address and read data. Must be >=0.
    parameter int PointerRamReadLatency = 0,
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
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalNotValid = 1,

    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth   = br_math::clamped_clog2(Depth)
) (
    input logic clk,
    input logic rst,

    // Push side
    input logic [NumWritePorts-1:0] push_valid,
    input logic [NumWritePorts-1:0] push_ready,
    input logic [NumWritePorts-1:0][Width-1:0] push_data,
    input logic [NumWritePorts-1:0][FifoIdWidth-1:0] push_fifo_id,
    input logic push_full,

    // Pop side
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0] pop_empty,

    // Data RAM Ports
    input logic [NumWritePorts-1:0] data_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] data_ram_wr_addr,
    input logic [NumWritePorts-1:0][Width-1:0] data_ram_wr_data,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data,

    // Pointer RAM Ports
    input logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_addr,
    input logic [NumWritePorts-1:0][AddrWidth-1:0] ptr_ram_wr_data,

    input logic [NumReadPorts-1:0] ptr_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_addr,
    input logic [NumReadPorts-1:0] ptr_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] ptr_ram_rd_data,

    // External arbiter interface
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_request,
    input logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant,
    input logic [NumReadPorts-1:0] arb_enable_priority_update
);

  localparam bit HasStagingBuffer = (DataRamReadLatency > 0) || RegisterPopOutputs;

  // ----------External arb model----------
  ext_arb_fv_monitor #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos)
  ) fv_arb (
      .clk,
      .rst,
      .arb_request,
      .arb_grant,
      .arb_enable_priority_update
  );

  // ----------Data Ram FV model----------
  br_fifo_fv_ram #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(DataRamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst,
      .ram_wr_valid(data_ram_wr_valid),
      .ram_wr_addr(data_ram_wr_addr),
      .ram_wr_data(data_ram_wr_data),
      .ram_rd_addr_valid(data_ram_rd_addr_valid),
      .ram_rd_addr(data_ram_rd_addr),
      .ram_rd_data_valid(data_ram_rd_data_valid),
      .ram_rd_data(data_ram_rd_data)
  );

  // ----------Ptr Ram FV model----------
  br_fifo_fv_ram #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(AddrWidth),
      .RamReadLatency(PointerRamReadLatency)
  ) fv_ptr_ram (
      .clk,
      .rst,
      .ram_wr_valid(ptr_ram_wr_valid),
      .ram_wr_addr(ptr_ram_wr_addr),
      .ram_wr_data(ptr_ram_wr_data),
      .ram_rd_addr_valid(ptr_ram_rd_addr_valid),
      .ram_rd_addr(ptr_ram_rd_addr),
      .ram_rd_data_valid(ptr_ram_rd_data_valid),
      .ram_rd_data(ptr_ram_rd_data)
  );

  // ----------FIFO basic checks----------
  br_fifo_shared_dynamic_basic_fpv_monitor #(
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .HasStagingBuffer(HasStagingBuffer),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) fv_checker (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data,
      .push_fifo_id,
      .pop_valid,
      .pop_ready,
      .pop_data
  );

endmodule : br_fifo_shared_dynamic_ctrl_ext_arbiter_fpv_monitor

bind br_fifo_shared_dynamic_ctrl_ext_arbiter br_fifo_shared_dynamic_ctrl_ext_arbiter_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .NumLinkedListsPerFifo(NumLinkedListsPerFifo),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RegisterDeallocation(RegisterDeallocation),
    .DataRamReadLatency(DataRamReadLatency),
    .PointerRamReadLatency(PointerRamReadLatency),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
