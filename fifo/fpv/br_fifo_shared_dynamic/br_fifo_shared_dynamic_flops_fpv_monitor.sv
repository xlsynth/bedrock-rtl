// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Shared Dynamic Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface) FPV monitor

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_flops_fpv_monitor #(
    parameter int NumWritePorts = 1,
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 3,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit RegisterDeallocation = 0,
    parameter int DataRamDepthTiles = 1,
    parameter int DataRamWidthTiles = 1,
    parameter int DataRamAddressDepthStages = 0,
    parameter int DataRamReadDataDepthStages = 0,
    parameter int DataRamReadDataWidthStages = 0,
    parameter int PointerRamDepthTiles = 1,
    parameter int PointerRamWidthTiles = 1,
    parameter int PointerRamAddressDepthStages = 0,
    parameter int PointerRamReadDataDepthStages = 0,
    parameter int PointerRamReadDataWidthStages = 0,
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

    // Pop side
    input logic [NumFifos-1:0] pop_valid,
    input logic [NumFifos-1:0] pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data
);

  localparam bit WolperColorEn = 0;
  logic [$clog2(Width)-1:0] magic_bit_index;
  `BR_ASSUME(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < Width))

  // ----------FIFO basic checks----------
  localparam int DataRamReadLatency =
      DataRamAddressDepthStages + DataRamReadDataDepthStages + DataRamReadDataWidthStages;
  localparam bit HasStagingBuffer = (DataRamReadLatency > 0) || RegisterPopOutputs;

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

endmodule : br_fifo_shared_dynamic_flops_fpv_monitor

bind br_fifo_shared_dynamic_flops br_fifo_shared_dynamic_flops_fpv_monitor #(
    .NumWritePorts(NumWritePorts),
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RegisterDeallocation(RegisterDeallocation),
    .DataRamDepthTiles(DataRamDepthTiles),
    .DataRamWidthTiles(DataRamWidthTiles),
    .DataRamAddressDepthStages(DataRamAddressDepthStages),
    .DataRamReadDataDepthStages(DataRamReadDataDepthStages),
    .DataRamReadDataWidthStages(DataRamReadDataWidthStages),
    .PointerRamDepthTiles(PointerRamDepthTiles),
    .PointerRamWidthTiles(PointerRamWidthTiles),
    .PointerRamAddressDepthStages(PointerRamAddressDepthStages),
    .PointerRamReadDataDepthStages(PointerRamReadDataDepthStages),
    .PointerRamReadDataWidthStages(PointerRamReadDataWidthStages),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
