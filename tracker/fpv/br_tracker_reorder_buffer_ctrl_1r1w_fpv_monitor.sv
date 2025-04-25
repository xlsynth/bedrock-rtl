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

// Bedrock-RTL 1R1W Reorder Buffer Controller

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_buffer_ctrl_1r1w_fpv_monitor #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = $clog2(NumEntries),
    // Width of the data payload. Must be at least 1.
    parameter int DataWidth = 1,
    // Number of clock cycles for the RAM read latency. Must be >=0.
    parameter int RamReadLatency = 0,
    // If 1, ensure that reordered_resp_pop_data comes directly from a register,
    // improving timing at the cost of an additional cycle of latency.
    parameter bit RegisterPopOutputs = 0,
    // If 1, then assert unordered_resp_push_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int MinEntryIdWidth = $clog2(NumEntries),
    localparam int EntryCountWidth = $clog2(NumEntries + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    input logic alloc_valid,
    input logic [EntryIdWidth-1:0] alloc_entry_id,

    // Unordered Response Interface
    input logic unordered_resp_push_valid,
    input logic [EntryIdWidth-1:0] unordered_resp_push_entry_id,
    input logic [DataWidth-1:0] unordered_resp_push_data,

    // Unordered Response Interface
    input logic reordered_resp_pop_ready,
    input logic reordered_resp_pop_valid,
    input logic [DataWidth-1:0] reordered_resp_pop_data,

    // Count Information
    input logic resp_pending,

    // 1R1W RAM Interface
    input logic [MinEntryIdWidth-1:0] ram_wr_addr,
    input logic ram_wr_valid,
    input logic [DataWidth-1:0] ram_wr_data,
    input logic [MinEntryIdWidth-1:0] ram_rd_addr,
    input logic ram_rd_addr_valid,
    input logic [DataWidth-1:0] ram_rd_data,
    input logic ram_rd_data_valid
);

  // ----------FV Modeling Code----------
  logic [NumEntries-1:0][DataWidth-1:0] fv_ram_data;

  `BR_REGLN(fv_ram_data[ram_wr_addr], ram_wr_data, ram_wr_valid)

  // ----------FV assumptions----------
  if (RamReadLatency == 0) begin : gen_latency0
    `BR_ASSUME(ram_rd_data_a, ram_rd_data == fv_ram_data[ram_rd_addr])
    `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid == ram_rd_addr_valid)
  end else begin : gen_latency_non0
    `BR_ASSUME(ram_rd_data_a, ram_rd_data == $past(fv_ram_data[ram_rd_addr], RamReadLatency))
    `BR_ASSUME(ram_rd_data_addr_latency_a, ram_rd_data_valid == $past(
               ram_rd_addr_valid, RamReadLatency))
  end

  // ----------tracker reorder buffer basic checks----------
  br_tracker_reorder_buffer_basic_fpv_monitor #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth),
      .DataWidth(DataWidth),
      .RamReadLatency(RamReadLatency)
  ) fv_checker (
      .clk,
      .rst,
      .alloc_ready,
      .alloc_valid,
      .alloc_entry_id,
      .unordered_resp_push_valid,
      .unordered_resp_push_entry_id,
      .unordered_resp_push_data,
      .reordered_resp_pop_ready,
      .reordered_resp_pop_valid,
      .reordered_resp_pop_data,
      .resp_pending
  );

endmodule : br_tracker_reorder_buffer_ctrl_1r1w_fpv_monitor

bind br_tracker_reorder_buffer_ctrl_1r1w br_tracker_reorder_buffer_ctrl_1r1w_fpv_monitor #(
    .NumEntries(NumEntries),
    .EntryIdWidth(EntryIdWidth),
    .DataWidth(DataWidth),
    .RamReadLatency(RamReadLatency),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
