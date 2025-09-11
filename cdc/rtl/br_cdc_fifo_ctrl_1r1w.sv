// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_gates.svh"

module br_cdc_fifo_ctrl_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data can come directly from the push interface
    // (if bypass is enabled), the RAM read interface, and/or an internal staging
    // buffer (if RAM read latency is >0).
    parameter bit RegisterPopOutputs = 0,
    // If 1 (the default), register push_rst on push_clk and pop_rst on pop_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless push_rst and pop_rst are driven directly by
    // registers.
    parameter bit RegisterResetActive = 1,
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
    // If 1, assert that push_valid is stable when backpressured.
    // If 0, cover that push_valid can be unstable.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    // If 0, cover that push_data can be unstable.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    // Posedge-triggered clock.
    input logic push_clk,
    // Synchronous active-high reset.
    input logic push_rst,

    // Push-side interface
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  push_full,
    output logic [CountWidth-1:0] push_slots,

    // Push-side RAM write interface
    output logic                 push_ram_wr_valid,
    output logic [AddrWidth-1:0] push_ram_wr_addr,
    output logic [    Width-1:0] push_ram_wr_data,

    // Posedge-triggered clock.
    input logic pop_clk,
    // Synchronous active-high reset.
    input logic pop_rst,

    // Pop-side interface
    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    // Pop-side status flags
    output logic                  pop_empty,
    output logic [CountWidth-1:0] pop_items,

    // Pop-side RAM read interface
    output logic                 pop_ram_rd_addr_valid,
    output logic [AddrWidth-1:0] pop_ram_rd_addr,
    input  logic                 pop_ram_rd_data_valid,
    input  logic [    Width-1:0] pop_ram_rd_data
);
  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [CountWidth-1:0] push_push_count_gray;
  logic [CountWidth-1:0] pop_pop_count_gray;
  logic                  push_reset_active_push;
  logic                  pop_reset_active_pop;

  br_cdc_fifo_ctrl_push_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterResetActive(RegisterResetActive),
      .RamWriteLatency(RamWriteLatency),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_ctrl_push_1r1w (
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
      .pop_reset_active_pop,
      .pop_pop_count_gray,
      .push_push_count_gray,
      .push_reset_active_push
  );

  br_cdc_fifo_ctrl_pop_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .RamReadLatency(RamReadLatency),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .NumSyncStages(NumSyncStages)
  ) br_cdc_fifo_ctrl_pop_1r1w_inst (
      .push_clk,
      .push_rst,
      .pop_reset_active_pop,
      .pop_pop_count_gray,
      .push_push_count_gray,
      .push_reset_active_push,
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

endmodule : br_cdc_fifo_ctrl_1r1w
