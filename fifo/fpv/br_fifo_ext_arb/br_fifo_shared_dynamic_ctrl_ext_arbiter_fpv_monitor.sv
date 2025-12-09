// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Shared Dynamic Multi-FIFO Controller (Push Valid/Ready Interface) with external
// arbiter interface

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_ctrl_ext_arbiter_fpv_monitor #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 2,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter int NumLinkedListsPerFifo = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterDeallocation = 0,
    parameter int DataRamReadLatency = 0,
    parameter int PointerRamReadLatency = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
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
  localparam bit WolperColorEn = 0;
  logic [$clog2(Width)-1:0] magic_bit_index;
  `BR_ASSUME(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < Width))

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
      .WolperColorEn(WolperColorEn),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(Width),
      .RamReadLatency(DataRamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst,
      .magic_bit_index,
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
      .WolperColorEn(0),
      .NumWritePorts(NumWritePorts),
      .NumReadPorts(NumReadPorts),
      .Depth(Depth),
      .Width(AddrWidth),
      .RamReadLatency(PointerRamReadLatency)
  ) fv_ptr_ram (
      .clk,
      .rst,
      .magic_bit_index('0),  // Not used
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
      .WolperColorEn(WolperColorEn),
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
