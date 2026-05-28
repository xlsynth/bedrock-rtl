// SPDX-License-Identifier: Apache-2.0

// Bind wrapper for the shared multi-FIFO credit pop-controller checker.

module br_fifo_shared_pop_ctrl_credit_fpv_monitor #(
    parameter int NumReadPorts = 1,
    parameter int NumFifos = 1,
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter int PopMaxCredits = 1,
    parameter bit RegisterDeallocation = 0,
    parameter int RamReadLatency = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CreditWidth = $clog2(PopMaxCredits + 1),
    localparam int FifoIdWidth = (NumFifos <= 1) ? 1 : $clog2(NumFifos)
) (
    input logic clk,
    input logic rst,

    input logic [NumFifos-1:0] head_valid,
    input logic [NumFifos-1:0] head_ready,
    input logic [NumFifos-1:0][AddrWidth-1:0] head,

    input logic [NumFifos-1:0] ram_empty,

    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [NumFifos-1:0] pop_credit,

    input logic [NumReadPorts-1:0] pop_valid,
    input logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id,
    input logic [NumReadPorts-1:0][Width-1:0] pop_data,

    input logic [NumFifos-1:0] pop_empty,

    input logic [NumFifos-1:0][CreditWidth-1:0] credit_initial_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_withhold_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_available_pop,
    input logic [NumFifos-1:0][CreditWidth-1:0] credit_count_pop,

    input logic [NumFifos-1:0] dealloc_valid,
    input logic [NumFifos-1:0][AddrWidth-1:0] dealloc_entry_id,

    input logic [NumReadPorts-1:0] data_ram_rd_addr_valid,
    input logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr,
    input logic [NumReadPorts-1:0] data_ram_rd_data_valid,
    input logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data
);

  br_fifo_shared_pop_ctrl_credit_fpv_checker #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .PopMaxCredits(PopMaxCredits),
      .RegisterDeallocation(RegisterDeallocation),
      .RamReadLatency(RamReadLatency)
  ) checker_inst (
      .clk,
      .rst,
      .head_valid,
      .head_ready,
      .head,
      .ram_empty,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_valid,
      .pop_fifo_id,
      .pop_data,
      .pop_empty,
      .credit_initial_pop,
      .credit_withhold_pop,
      .credit_available_pop,
      .credit_count_pop,
      .dealloc_valid,
      .dealloc_entry_id,
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data
  );

endmodule : br_fifo_shared_pop_ctrl_credit_fpv_monitor

bind br_fifo_shared_pop_ctrl_credit br_fifo_shared_pop_ctrl_credit_fpv_monitor #(
    .NumReadPorts(NumReadPorts),
    .NumFifos(NumFifos),
    .Depth(Depth),
    .Width(Width),
    .PopMaxCredits(PopMaxCredits),
    .RegisterDeallocation(RegisterDeallocation),
    .RamReadLatency(RamReadLatency)
) monitor (.*);
