// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for losing a second pushed tail when the popped head is reused.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_linked_list_ctrl_reuse_tail_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int Depth = 4;
  localparam int NumWritePorts = 2;
  localparam int NumLinkedLists = 1;
  localparam int RamReadLatency = 0;
  localparam int AddressWidth = $clog2(Depth);
  localparam int CountWidth = $clog2(Depth + 1);

  logic [2:0] cycle;
  logic [NumWritePorts-1:0] next_tail_valid;
  logic [NumWritePorts-1:0][AddressWidth-1:0] next_tail;
  logic head_valid;
  logic head_ready;
  logic [AddressWidth-1:0] head;
  logic empty;
  logic [CountWidth-1:0] items;
  logic [NumWritePorts-1:0] ptr_ram_wr_valid;
  logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_addr;
  logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_data;
  logic ptr_ram_rd_addr_valid;
  logic [AddressWidth-1:0] ptr_ram_rd_addr;
  logic ptr_ram_rd_data_valid;
  logic [AddressWidth-1:0] ptr_ram_rd_data;

  br_tracker_linked_list_ctrl #(
      .Depth(Depth),
      .NumWritePorts(NumWritePorts),
      .NumLinkedLists(NumLinkedLists),
      .RamReadLatency(RamReadLatency)
  ) dut (
      .clk,
      .rst,
      .next_tail_valid,
      .next_tail,
      .head_valid,
      .head_ready,
      .head,
      .empty,
      .items,
      .ptr_ram_wr_valid,
      .ptr_ram_wr_addr,
      .ptr_ram_wr_data,
      .ptr_ram_rd_addr_valid,
      .ptr_ram_rd_addr,
      .ptr_ram_rd_data_valid,
      .ptr_ram_rd_data
  );

  br_ram_flops #(
      .Depth(Depth),
      .Width(AddressWidth),
      .NumWritePorts(NumWritePorts)
  ) ptr_ram (
      .wr_clk(clk),
      .wr_rst(rst),
      .wr_valid(ptr_ram_wr_valid),
      .wr_addr(ptr_ram_wr_addr),
      .wr_data(ptr_ram_wr_data),
      .wr_word_en({NumWritePorts{1'b1}}),
      .rd_clk(clk),
      .rd_rst(rst),
      .rd_addr_valid(ptr_ram_rd_addr_valid),
      .rd_addr(ptr_ram_rd_addr),
      .rd_data_valid(ptr_ram_rd_data_valid),
      .rd_data(ptr_ram_rd_data)
  );

  assign next_tail_valid = !rst && cycle == 3'd0 ? 2'b01 :
                           !rst && cycle == 3'd2 ? 2'b11 : '0;
  assign next_tail[0] = cycle == 3'd0 || cycle == 3'd2 ? 2'd2 : '0;
  assign next_tail[1] = cycle == 3'd2 ? 2'd1 : '0;
  assign head_ready = !rst && (cycle == 3'd2 || cycle == 3'd4);

  `BR_REG(cycle, cycle + 3'd1)

  `BR_ASSERT(initial_head_a, cycle == 3'd1 |-> head_valid && head == 2'd2 && items == 1)
  `BR_ASSERT(reused_entry_head_a, cycle == 3'd3 |-> head_valid && head == 2'd2 && items == 2)
  `BR_ASSERT(second_tail_follows_reused_entry_a,
             cycle == 3'd4 && head_ready && head_valid && head == 2'd2 |=>
                 head_valid && head == 2'd1)

endmodule : br_tracker_linked_list_ctrl_reuse_tail_fpv_repro
