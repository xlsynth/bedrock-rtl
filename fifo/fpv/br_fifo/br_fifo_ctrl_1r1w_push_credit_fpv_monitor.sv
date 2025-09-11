// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_fifo_ctrl_1r1w_push_credit_fpv_monitor #(
    parameter int Depth = 2,  // Number of entries in the FIFO. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the FIFO. Must be at least 1.
    parameter bit EnableBypass = 1,
    parameter int MaxCredit = Depth,
    parameter bit RegisterPushOutputs = 0,
    parameter bit RegisterPopOutputs = 0,
    parameter int RamReadLatency = 0,
    // The actual depth of the RAM. This may be smaller than the FIFO depth
    // if EnableBypass is 1 and RamReadLatency is >0 or RegisterPopOutputs is 1.
    // The minimum RAM depth would be (Depth - RamReadLatency - 1) or 1
    // if Depth is less than or equal to RamReadLatency + 1.
    // If bypass is disabled or RamReadLatency and RegisterPopOutputs are both 0,
    // the minimum RAM depth is Depth.
    // The RAM depth may be made larger than the minimum if convenient (e.g. the
    // backing RAM is an SRAM of slightly larger depth than the FIFO depth).
    parameter int RamDepth = Depth,
    localparam int AddrWidth = br_math::clamped_clog2(RamDepth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic             push_sender_in_reset,
    input logic             push_receiver_in_reset,
    input logic             push_credit_stall,
    input logic             push_credit,
    input logic             push_valid,
    input logic [Width-1:0] push_data,

    // Pop-side interface
    input logic             pop_ready,
    input logic             pop_valid,
    input logic [Width-1:0] pop_data,

    // Push-side status flags
    input logic                  full,
    input logic                  full_next,
    input logic [CountWidth-1:0] slots,
    input logic [CountWidth-1:0] slots_next,

    // Pop-side status flags
    input logic                  empty,
    input logic                  empty_next,
    input logic [CountWidth-1:0] items,
    input logic [CountWidth-1:0] items_next,

    // Push-side credits
    input logic [CreditWidth-1:0] credit_initial_push,
    input logic [CreditWidth-1:0] credit_withhold_push,
    input logic [CreditWidth-1:0] credit_count_push,
    input logic [CreditWidth-1:0] credit_available_push,

    // 1R1W RAM interface
    input logic                 ram_wr_valid,
    input logic [AddrWidth-1:0] ram_wr_addr,
    input logic [    Width-1:0] ram_wr_data,
    input logic                 ram_rd_addr_valid,
    input logic [AddrWidth-1:0] ram_rd_addr,
    input logic                 ram_rd_data_valid,
    input logic [    Width-1:0] ram_rd_data
);

  // ----------Instantiate credit FV checker----------
  br_credit_receiver_fpv_monitor #(
      .PStatic(0),
      .MaxCredit(MaxCredit),
      .NumWritePorts(1)
  ) br_credit_receiver_fpv_monitor (
      .clk,
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall,
      .push_credit,
      .push_valid,
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .config_base ('d0),
      .config_bound('d0)
  );

  // ----------Data Ram FV model----------
  br_fifo_fv_ram #(
      .NumWritePorts(1),
      .NumReadPorts(1),
      .Depth(RamDepth),
      .Width(Width),
      .RamReadLatency(RamReadLatency)
  ) fv_data_ram (
      .clk,
      .rst,
      .ram_wr_valid(ram_wr_valid),
      .ram_wr_addr(ram_wr_addr),
      .ram_wr_data(ram_wr_data),
      .ram_rd_addr_valid(ram_rd_addr_valid),
      .ram_rd_addr(ram_rd_addr),
      .ram_rd_data_valid(ram_rd_data_valid),
      .ram_rd_data(ram_rd_data)
  );

  // ----------FIFO basic checks----------
  br_fifo_basic_fpv_monitor #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .EnableCoverPushBackpressure(0)
  ) br_fifo_basic_fpv_monitor (
      .clk,
      .rst,
      .push_ready(1'b1),
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .empty,
      .empty_next,
      .items,
      .items_next
  );

endmodule : br_fifo_ctrl_1r1w_push_credit_fpv_monitor

bind br_fifo_ctrl_1r1w_push_credit br_fifo_ctrl_1r1w_push_credit_fpv_monitor #(
    .Depth(Depth),
    .Width(Width),
    .EnableBypass(EnableBypass),
    .MaxCredit(MaxCredit),
    .RegisterPushOutputs(RegisterPushOutputs),
    .RegisterPopOutputs(RegisterPopOutputs),
    .RamReadLatency(RamReadLatency),
    .RamDepth(RamDepth)
) monitor (.*);
