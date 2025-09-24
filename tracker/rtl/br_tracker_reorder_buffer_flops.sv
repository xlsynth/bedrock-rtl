// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Reorder Buffer (Flops Storage)
//
// Implements a reorder buffer using flops for storage.

module br_tracker_reorder_buffer_flops #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = 1,
    // Width of the data payload.
    parameter int DataWidth = 1,
    // If 1, ensure that the reordered_resp_pop_valid and reordered_resp_pop_data
    // come directly from registers, improving timing at the cost of an
    // additional cycle of latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, then assert unordered_resp_push_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    output logic alloc_valid,
    output logic [EntryIdWidth-1:0] alloc_entry_id,

    // Unordered Response Interface
    input logic unordered_resp_push_valid,
    input logic [EntryIdWidth-1:0] unordered_resp_push_entry_id,
    input logic [DataWidth-1:0] unordered_resp_push_data,

    // Reordered Response Interface
    input logic reordered_resp_pop_ready,
    output logic reordered_resp_pop_valid,
    output logic [DataWidth-1:0] reordered_resp_pop_data,

    // Count Information
    output logic resp_pending
);
  localparam int MinEntryIdWidth = $clog2(NumEntries);

  logic [MinEntryIdWidth-1:0] ram_wr_addr;
  logic ram_wr_valid;
  logic [DataWidth-1:0] ram_wr_data;
  logic [MinEntryIdWidth-1:0] ram_rd_addr;
  logic ram_rd_addr_valid;
  logic [DataWidth-1:0] ram_rd_data;
  logic ram_rd_data_valid;

  br_tracker_reorder_buffer_ctrl_1r1w #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth),
      .DataWidth(DataWidth),
      .RamReadLatency(0),
      .RegisterPopOutputs(RegisterPopOutputs),
      .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
  ) br_tracker_reorder_buffer_ctrl_1r1w_inst (
      .clk,
      .rst,
      //
      .alloc_ready,
      .alloc_valid,
      .alloc_entry_id,
      //
      .unordered_resp_push_valid,
      .unordered_resp_push_entry_id,
      .unordered_resp_push_data,
      //
      .reordered_resp_pop_ready,
      .reordered_resp_pop_valid,
      .reordered_resp_pop_data,
      //
      .resp_pending,
      //
      .ram_wr_addr,
      .ram_wr_valid,
      .ram_wr_data,
      .ram_rd_addr,
      .ram_rd_addr_valid,
      .ram_rd_data,
      .ram_rd_data_valid
  );

  br_ram_flops #(
      .Depth(NumEntries),
      .Width(DataWidth),
      .NumReadPorts(1),
      .NumWritePorts(1)
  ) br_ram_flops_reorder_buffer (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(ram_wr_valid),
      .wr_addr(ram_wr_addr),
      .wr_data(ram_wr_data),
      .wr_word_en(1'b1),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(ram_rd_addr_valid),
      .rd_addr(ram_rd_addr),
      .rd_data_valid(ram_rd_data_valid),
      .rd_data(ram_rd_data)
  );

endmodule
