// SPDX-License-Identifier: Apache-2.0


// Pop-side of Bedrock-RTL CDC FIFO Controller (1R1W, Ready/Valid Variant)
//
// The pop side of a one-read/one-write (1R1W) asynchronous FIFO controller
// that uses the AMBA-inspired ready-valid handshake protocol for synchronizing
// pipeline stages and stalling when encountering backpressure hazards.
//
// This module is intended to connect to an instance of br_cdc_fifo_ctrl_push_1r1w
// or br_cdc_fifo_ctrl_push_1r1w_push_credit, as well as a 1R1W RAM module.
//
// Ordinarily the push and pop sides of the FIFO controller can be connected
// together directly. If necessary, they can be separated, for example to
// implement a CDC crossing across a boundary where the sending and receiving
// flops must be separated or logic needs to be placed in between the two sides.

`include "br_asserts_internal.svh"
`include "br_gates.svh"

module br_cdc_fifo_ctrl_pop_1r1w #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    // If 1, then ensure pop_valid/pop_data always come directly from a register
    // at the cost of an additional pop cycle of cut-through latency.
    // If 0, pop_valid/pop_data can come directly from the push interface
    // (if bypass is enabled), the RAM read interface, and/or an internal staging
    // buffer (if RAM read latency is >0).
    parameter bit RegisterPopOutputs = 0,
    // If 1 (the default), register pop_rst on pop_clk before sending it out
    // as pop_reset_active_pop. This adds an extra cycle to the backpressure
    // latency of the FIFO.
    // Do not set this to 0 unless either pop_rst is driven directly by a
    // register or if pop_reset_active_pop is registered externally
    // before synchronization to the push clock domain.
    parameter bit RegisterResetActive = 1,
    // The number of pop cycles between when ram_rd_addr_valid is asserted and
    // ram_rd_data_valid is asserted.
    parameter int RamReadLatency = 0,
    // The number of synchronization stages to use for the gray counts.
    parameter int NumSyncStages = 3,
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

    // Signals that connect to the push side.
    output logic                  pop_reset_active_pop,
    output logic [CountWidth-1:0] pop_pop_count_gray,
    input  logic [CountWidth-1:0] push_push_count_gray,
    input  logic                  push_reset_active_push,

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

  logic [CountWidth-1:0] pop_push_count_gray;
  logic                  pop_reset_active_push;
  logic [     Width-1:0] pop_ram_rd_data_maxdel;

  br_cdc_fifo_gray_count_sync #(
      .CountWidth(CountWidth),
      .NumStages (NumSyncStages)
  ) br_cdc_fifo_gray_count_sync_push2pop (
      // TODO(zhemao): Remove need for push_clk and push_rst here.
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(push_rst),
      .src_count_gray(push_push_count_gray),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(pop_rst),
      .dst_count_gray(pop_push_count_gray)
  );

  br_cdc_bit_toggle #(
      .NumStages(NumSyncStages),
      .AddSourceFlop(0)
  ) br_cdc_bit_toggle_reset_active_push (
      .src_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .src_rst(push_rst),
      .src_bit(push_reset_active_push),
      .dst_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .dst_rst(pop_rst),
      .dst_bit(pop_reset_active_push)
  );

  br_cdc_fifo_pop_ctrl #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .RamReadLatency(RamReadLatency),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_cdc_fifo_pop_ctrl (
      .clk              (pop_clk),                 // ri lint_check_waive SAME_CLOCK_NAME
      .rst              (pop_rst),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty            (pop_empty),
      .items            (pop_items),
      .ram_rd_addr_valid(pop_ram_rd_addr_valid),
      .ram_rd_addr      (pop_ram_rd_addr),
      .ram_rd_data_valid(pop_ram_rd_data_valid),
      .ram_rd_data      (pop_ram_rd_data_maxdel),
      .push_count_gray  (pop_push_count_gray),
      .pop_count_gray   (pop_pop_count_gray),
      .reset_active_pop (pop_reset_active_pop),
      .reset_active_push(pop_reset_active_push)
  );

  // Tag this signal as needing max delay checks
  // ri lint_check_off ONE_CONN_PER_LINE
  `BR_GATE_CDC_MAXDEL_BUS(pop_ram_rd_data_maxdel, pop_ram_rd_data, Width)
  // ri lint_check_on ONE_CONN_PER_LINE

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(no_pop_valid_when_empty_a, pop_empty |-> !pop_valid, pop_clk, pop_rst)

endmodule : br_cdc_fifo_ctrl_pop_1r1w
