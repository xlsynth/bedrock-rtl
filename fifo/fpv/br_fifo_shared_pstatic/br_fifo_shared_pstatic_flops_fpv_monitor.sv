// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Shared Pseudo-Static Multi-FIFO with Flop-based Storage (Push Valid/Ready Interface)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pstatic_flops_fpv_monitor #(
    parameter int NumFifos = 2,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int StagingBufferDepth = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamDepthTiles = 1,
    parameter int RamWidthTiles = 1,
    parameter int RamAddressDepthStages = 0,
    parameter int RamReadDataDepthStages = 0,
    parameter int RamReadDataWidthStages = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int FifoIdWidth = br_math::clamped_clog2(NumFifos),
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
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
    input logic config_error,

    // Push side
    input logic                   push_valid,
    input logic                   push_ready,
    input logic [      Width-1:0] push_data,
    input logic [FifoIdWidth-1:0] push_fifo_id,
    input logic [   NumFifos-1:0] push_full,

    // Pop side
    input logic [NumFifos-1:0]            pop_valid,
    input logic [NumFifos-1:0]            pop_ready,
    input logic [NumFifos-1:0][Width-1:0] pop_data,
    input logic [NumFifos-1:0]            pop_empty
);

  localparam bit WolperColorEn = 0;
  logic [$clog2(Width)-1:0] magic_bit_index;
  `BR_ASSUME(magic_bit_index_range_a, $stable(magic_bit_index) && (magic_bit_index < Width))

  localparam int RamReadLatency = RamAddressDepthStages +
                                  RamReadDataDepthStages +
                                  RamReadDataWidthStages;

  // ----------FIFO basic checks----------
  br_fifo_shared_pstatic_basic_fpv_monitor #(
      .WolperColorEn(WolperColorEn),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .StagingBufferDepth(StagingBufferDepth),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) fv_checker (
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
      .pop_empty
  );

endmodule : br_fifo_shared_pstatic_flops_fpv_monitor

bind br_fifo_shared_pstatic_flops br_fifo_shared_pstatic_flops_fpv_monitor #(
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .StagingBufferDepth(StagingBufferDepth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RamDepthTiles(RamDepthTiles),
    .RamWidthTiles(RamWidthTiles),
    .RamAddressDepthStages(RamAddressDepthStages),
    .RamReadDataDepthStages(RamReadDataDepthStages),
    .RamReadDataWidthStages(RamReadDataWidthStages),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
