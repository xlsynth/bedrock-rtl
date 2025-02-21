// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Implements a reorder buffer using flops for storage.

module br_tracker_reorder_buffer_flops #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = 1,
    // Width of the data payload.
    parameter int DataWidth = 1,
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    output logic alloc_valid,
    output logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic dealloc_valid,
    input logic [EntryIdWidth-1:0] dealloc_entry_id,
    input logic [DataWidth-1:0] dealloc_data,

    // Deallocation Complete Interface
    input logic dealloc_complete_ready,
    output logic dealloc_complete_valid,
    output logic [EntryIdWidth-1:0] dealloc_complete_entry_id,
    output logic [DataWidth-1:0] dealloc_complete_data
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
      .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
  ) br_tracker_reorder_buffer_ctrl_1r1w_inst (
      .clk,
      .rst,
      //
      .alloc_ready,
      .alloc_valid,
      .alloc_entry_id,
      //
      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_data,
      //
      .dealloc_complete_ready,
      .dealloc_complete_valid,
      .dealloc_complete_entry_id,
      .dealloc_complete_data,
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
