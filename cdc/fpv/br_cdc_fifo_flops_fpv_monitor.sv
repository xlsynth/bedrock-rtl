// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL CDC FIFO (Internal 1R1W Flop-RAM, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_flops_fpv_monitor #(
    parameter bit Jasper = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter int NumSyncStages = 3,
    parameter int FlopRamDepthTiles = 1,
    parameter int FlopRamWidthTiles = 1,
    parameter int FlopRamAddressDepthStages = 0,
    parameter int FlopRamReadDataDepthStages = 0,
    parameter int FlopRamReadDataWidthStages = 0,
    parameter bit EnableStructuredGatesDataQualification = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
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
      .Jasper(Jasper),
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
      .pop_valid(pop_valid && !pop_rst),
      .pop_data,
      .push_full,
      .push_slots,
      .pop_empty,
      .pop_items
  );

  `BR_ASSERT_CR(no_valid_data_stable_a, ##1 !pop_valid && !$fell(pop_valid) |-> $stable(pop_data),
                pop_clk, pop_rst)

endmodule : br_cdc_fifo_flops_fpv_monitor
