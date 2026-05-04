// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for delayed pop data being reported while pop_empty is high.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_pop_ctrl_credit_ext_arbiter_pop_empty_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int NumReadPorts = 1;
  localparam int NumFifos = 2;
  localparam int Depth = 4;
  localparam int Width = 8;
  localparam int PopMaxCredits = 1;
  localparam int RamReadLatency = 1;

  localparam int AddrWidth = $clog2(Depth);
  localparam int CreditWidth = $clog2(PopMaxCredits + 1);
  localparam int FifoIdWidth = $clog2(NumFifos);

  logic [NumFifos-1:0] head_valid;
  logic [NumFifos-1:0] head_ready;
  logic [NumFifos-1:0][AddrWidth-1:0] head;
  logic [NumFifos-1:0] ram_empty;
  logic pop_sender_in_reset;
  logic pop_receiver_in_reset;
  logic [NumFifos-1:0] pop_credit;
  logic [NumReadPorts-1:0] pop_valid;
  logic [NumReadPorts-1:0][FifoIdWidth-1:0] pop_fifo_id;
  logic [NumReadPorts-1:0][Width-1:0] pop_data;
  logic [NumFifos-1:0] pop_empty;
  logic [NumFifos-1:0][CreditWidth-1:0] credit_initial_pop;
  logic [NumFifos-1:0][CreditWidth-1:0] credit_withhold_pop;
  logic [NumReadPorts-1:0] data_ram_rd_addr_valid;
  logic [NumReadPorts-1:0][AddrWidth-1:0] data_ram_rd_addr;
  logic [NumReadPorts-1:0] data_ram_rd_data_valid;
  logic [NumReadPorts-1:0][Width-1:0] data_ram_rd_data;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_request;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_grant;
  logic [NumReadPorts-1:0][NumFifos-1:0] arb_can_grant;
  logic [NumReadPorts-1:0] arb_enable_priority_update;
  logic item_present;
  logic item_present_next;

  br_fifo_shared_pop_ctrl_credit_ext_arbiter #(
      .NumReadPorts(NumReadPorts),
      .NumFifos(NumFifos),
      .Depth(Depth),
      .Width(Width),
      .PopMaxCredits(PopMaxCredits),
      .RamReadLatency(RamReadLatency)
  ) dut (
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
      .credit_available_pop(),
      .credit_count_pop(),
      .dealloc_valid(),
      .dealloc_entry_id(),
      .data_ram_rd_addr_valid,
      .data_ram_rd_addr,
      .data_ram_rd_data_valid,
      .data_ram_rd_data,
      .arb_request,
      .arb_grant,
      .arb_can_grant,
      .arb_enable_priority_update
  );

  assign pop_receiver_in_reset = 1'b0;
  assign pop_credit = '0;
  assign credit_initial_pop[0] = CreditWidth'(1);
  assign credit_initial_pop[1] = '0;
  assign credit_withhold_pop = '0;
  assign head_valid[0] = item_present;
  assign head_valid[1] = 1'b0;
  assign head = '0;
  assign ram_empty[0] = !item_present;
  assign ram_empty[1] = 1'b1;
  assign arb_grant[0][0] = arb_request[0][0];
  assign arb_grant[0][1] = 1'b0;
  assign arb_can_grant = arb_grant;
  assign item_present_next = item_present && !(head_valid[0] && head_ready[0]);
  assign data_ram_rd_data[0] = 8'h5a;

  `BR_REGI(item_present, item_present_next, 1'b1)
  `BR_REG(data_ram_rd_data_valid[0], data_ram_rd_addr_valid[0])

  `BR_ASSERT(pop_empty_matches_delivered_data_a,
             pop_valid[0] && pop_fifo_id[0] == '0 |-> !pop_empty[0])

endmodule : br_fifo_shared_pop_ctrl_credit_ext_arbiter_pop_empty_fpv_repro
