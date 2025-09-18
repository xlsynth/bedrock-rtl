// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL CDC FIFO (Internal 1R1W Flop-RAM, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_flops_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data comes directly from push_valid (if bypass is enabled)
    // and/or ram_wr_data.
    parameter bit RegisterPopOutputs = 0,
    // Number of synchronization stages to use for the gray counts. Must be >=2.
    parameter int NumSyncStages = 3,
    // Number of tiles in the depth (address) dimension. Must be at least 1 and evenly divide Depth.
    parameter int FlopRamDepthTiles = 1,
    // Number of tiles along the width (data) dimension. Must be at least 1 and evenly divide Width.
    parameter int FlopRamWidthTiles = 1,
    // Number of pipeline register stages inserted along the write address and read address paths
    // in the depth dimension. Must be at least 0.
    parameter int FlopRamAddressDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the depth dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataDepthStages = 0,
    // Number of pipeline register stages inserted along the read data path in the width dimension.
    // Must be at least 0.
    parameter int FlopRamReadDataWidthStages = 0,
    // If 1 then the read data is qualified with the rd_data_valid signal, 0 when not valid. Should
    // generally always be 1, unless gating logic is managed externally (including netlist-level
    // concerns!).
    parameter bit EnableStructuredGatesDataQualification = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,

    // Internal computed parameters
    localparam int AddrWidth  = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    // Push-side interface.
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface.
    input logic pop_clk,
    input logic pop_rst,
    input logic pop_ready
);

  localparam int RamReadLatency =
      FlopRamAddressDepthStages + FlopRamReadDataDepthStages + FlopRamReadDataWidthStages;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;

  // DUT primary outputs
  logic                  push_ready;
  logic                  pop_valid;
  logic [     Width-1:0] pop_data;
  // Push-side status flags
  logic                  push_full;
  logic [CountWidth-1:0] push_slots;
  // Pop-side status flags
  logic                  pop_empty;
  logic [CountWidth-1:0] pop_items;

  // ----------Instantiate DUT----------
  br_cdc_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumSyncStages(NumSyncStages),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableStructuredGatesDataQualification(EnableStructuredGatesDataQualification),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) dut (
      .push_clk,
      .push_rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .push_full,
      .push_slots,
      .pop_empty,
      .pop_items
  );

  // ----------Instantiate CDC FIFO FV basic checks----------
  br_cdc_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency)
  ) fv_checker (
      .clk,
      .rst,
      .push_clk,
      .push_rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .push_full,
      .push_slots,
      .pop_empty,
      .pop_items
  );

  `BR_ASSERT_CR(no_valid_data_stable_a, ##1 !pop_valid && !$fell(pop_valid) |-> $stable(pop_data),
                pop_clk, pop_rst)

endmodule : br_cdc_fifo_flops_fpv_monitor
