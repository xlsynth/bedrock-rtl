// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Linked List Controller FPV checker

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_linked_list_ctrl_fpv_monitor #(
    parameter int Depth = 2,
    parameter int NumWritePorts = 1,
    parameter int NumLinkedLists = 1,
    parameter int RamReadLatency = 0,
    localparam int AddressWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1)
) (
    input logic clk,
    input logic rst,

    input logic [NumWritePorts-1:0] next_tail_valid,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] next_tail,

    input logic head_valid,
    input logic head_ready,
    input logic [AddressWidth-1:0] head,

    input logic empty,
    input logic [CountWidth-1:0] items,

    input logic [NumWritePorts-1:0] ptr_ram_wr_valid,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_addr,
    input logic [NumWritePorts-1:0][AddressWidth-1:0] ptr_ram_wr_data,

    input logic ptr_ram_rd_addr_valid,
    input logic [AddressWidth-1:0] ptr_ram_rd_addr,
    input logic ptr_ram_rd_data_valid,
    input logic [AddressWidth-1:0] ptr_ram_rd_data
);

  // ----------FV modeling code----------
  logic [Depth-1:0] fv_entry_used, fv_entry_used_nxt;
  logic [Depth-1:0][AddressWidth-1:0] fv_ram;

  // bit vector tracking which entry of RAM is in use
  always_comb begin
    fv_entry_used_nxt = fv_entry_used;
    for (int i = 0; i < NumWritePorts; i++) begin
      `BR_ASSUME(tail_unique_a, next_tail_valid[i] |-> !fv_entry_used_nxt[next_tail[i]])
      if (next_tail_valid[i]) begin
        fv_entry_used_nxt[next_tail[i]] = 1'd1;
      end
    end
    if (head_valid & head_ready) begin
      fv_entry_used_nxt[head] = 1'd0;
    end
  end

  `BR_REG(fv_entry_used, fv_entry_used_nxt)

  // model FV ram
  always_ff @(posedge clk) begin
    for (int i = 0; i < NumWritePorts; i++) begin
      if (ptr_ram_wr_valid[i]) begin
        fv_ram[ptr_ram_wr_addr[i]] <= ptr_ram_wr_data[i];
      end
    end
  end

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumWritePorts; n++) begin : gen_asm
    `BR_ASSUME(tail_in_range_a, next_tail_valid[n] |-> next_tail[n] < Depth)
    `BR_ASSUME(tail_not_in_use_a, next_tail_valid[n] |-> !fv_entry_used[next_tail[n]])
  end
  // model RAM read data
  if (RamReadLatency == 0) begin : gen_latency0
    `BR_ASSUME(ram_rd_data_a, ptr_ram_rd_data == fv_ram[ptr_ram_rd_addr])
    `BR_ASSUME(ram_rd_data_addr_latency_a, ptr_ram_rd_data_valid == ptr_ram_rd_addr_valid)
  end else begin : gen_latency_non0
    `BR_ASSUME(ram_rd_data_a, ptr_ram_rd_data == $past(fv_ram[ptr_ram_rd_addr], RamReadLatency))
    `BR_ASSUME(ram_rd_data_addr_latency_a, ptr_ram_rd_data_valid == $past(
               ptr_ram_rd_addr_valid, RamReadLatency))
  end

  // ----------FV assertions----------
  `BR_ASSERT(head_valid_ready_a, head_valid && !head_ready |=> head_valid && $stable(head))
  `BR_ASSERT(empty_check_a, (fv_entry_used == 'd0) == empty)
  `BR_ASSERT(items_check_a, $countones(fv_entry_used) == items)

  // ----------Data integrity/ordering Check----------
  // If there are multiple writes on the same cycle,
  // the order will be from least significant write port to most significant.
  // This is jasper_scoreboard_3 default PORT_ORDER
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(AddressWidth),
      .IN_CHUNKS(NumWritePorts),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(Depth)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(next_tail_valid),
      .incoming_data(next_tail),
      .outgoing_vld(head_valid & head_ready),
      .outgoing_data(head)
  );

  // ----------Critical Covers----------
  `BR_COVER(all_next_tail_valid_c, &next_tail_valid)
  `BR_COVER(all_entry_used_c, &fv_entry_used)

endmodule : br_tracker_linked_list_ctrl_fpv_monitor

bind br_tracker_linked_list_ctrl br_tracker_linked_list_ctrl_fpv_monitor #(
    .Depth(Depth),
    .NumWritePorts(NumWritePorts),
    .NumLinkedLists(NumLinkedLists),
    .RamReadLatency(RamReadLatency)
) monitor (.*);
