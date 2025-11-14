// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL CDC FIFO Controller (1R1W, Push Ready/Valid, Pop Ready/Valid Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_cdc_fifo_ctrl_1r1w_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit RegisterPopOutputs = 0,
    // The number of push cycles after ram_wr_valid is asserted at which
    // it is safe to read the newly written data.
    parameter int RamWriteLatency = 1,
    // The number of pop cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
    // The number of synchronization stages to use for the gray counts.
    parameter int NumSyncStages = 3,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // FV system clk and rst
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic             push_clk,
    input logic             push_rst,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface
    input logic pop_clk,
    input logic pop_rst,
    input logic pop_ready,

    // Pop-side RAM read interface
    input logic             pop_ram_rd_data_valid,
    input logic [Width-1:0] pop_ram_rd_data
);
  // Push-side output signals
  logic                             push_ready;
  // Push-side status flags
  logic                             push_full;
  logic [CountWidth-1:0]            push_slots;
  // Push-side RAM write interface
  logic                             push_ram_wr_valid;
  logic [ AddrWidth-1:0]            push_ram_wr_addr;
  logic [     Width-1:0]            push_ram_wr_data;

  // Pop-side output signals
  logic                             pop_valid;
  logic [     Width-1:0]            pop_data;
  // Pop-side status flags
  logic                             pop_empty;
  logic [CountWidth-1:0]            pop_items;
  // Pop-side RAM read interface
  logic                             pop_ram_rd_addr_valid;
  logic [ AddrWidth-1:0]            pop_ram_rd_addr;

  // ----------FV Modeling Code----------
  logic [     Depth-1:0][Width-1:0] fv_ram_data;

  `BR_REGLNX(fv_ram_data[push_ram_wr_addr], push_ram_wr_data, push_ram_wr_valid, push_clk)

  // ----------FV assumptions----------
  if (RamReadLatency == 0) begin : gen_latency0
    `BR_ASSUME_CR(ram_rd_data_a, pop_ram_rd_data == fv_ram_data[pop_ram_rd_addr], pop_clk, pop_rst)
    `BR_ASSUME_CR(ram_rd_data_addr_latency_a,
                  pop_ram_rd_data_valid == pop_ram_rd_addr_valid && !pop_rst, pop_clk, pop_rst)
  end else begin : gen_latency_non0
    `BR_ASSUME_CR(ram_rd_data_a, pop_ram_rd_data == fv_ram_data[$past(
                  pop_ram_rd_addr, RamReadLatency)], pop_clk, pop_rst)
    `BR_ASSUME_CR(ram_rd_data_addr_latency_a, pop_ram_rd_data_valid == $past(
                  pop_ram_rd_addr_valid && !pop_rst, RamReadLatency), pop_clk, pop_rst)
  end

  // ----------Instantiate DUT----------
  br_cdc_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) dut (
      .push_clk,
      .push_rst,
      .push_ready,
      .push_valid,
      .push_data,
      .push_full,
      .push_slots,
      .push_ram_wr_valid,
      .push_ram_wr_addr,
      .push_ram_wr_data,
      .pop_clk,
      .pop_rst,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty,
      .pop_items,
      .pop_ram_rd_addr_valid,
      .pop_ram_rd_addr,
      .pop_ram_rd_data_valid,
      .pop_ram_rd_data
  );

  // ----------Instantiate CDC FIFO FV basic checks----------
  br_cdc_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
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

endmodule : br_cdc_fifo_ctrl_1r1w_fpv_monitor
