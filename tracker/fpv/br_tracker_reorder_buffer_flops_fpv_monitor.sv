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

// Bedrock-RTL Reorder Buffer (Flops Storage)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_buffer_flops_fpv_monitor #(
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
    input logic resp_pending
);

  // ----------tracker reorder buffer basic checks----------
  br_tracker_reorder_buffer_basic_fpv_monitor #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth),
      .DataWidth(DataWidth),
      .RamReadLatency(0)
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

endmodule : br_tracker_reorder_buffer_flops_fpv_monitor

bind br_tracker_reorder_buffer_flops br_tracker_reorder_buffer_flops_fpv_monitor #(
    .NumEntries(NumEntries),
    .EntryIdWidth(EntryIdWidth),
    .DataWidth(DataWidth),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
