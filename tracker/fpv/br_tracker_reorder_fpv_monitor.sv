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

// Bedrock-RTL Reordering Tracker

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_fpv_monitor #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = $clog2(NumEntries),
    // If 1, then assert dealloc_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    input logic alloc_valid,
    input logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic dealloc_valid,
    input logic [EntryIdWidth-1:0] dealloc_entry_id,

    // Deallocation Complete Interface
    input logic dealloc_complete_ready,
    input logic dealloc_complete_valid,
    input logic [EntryIdWidth-1:0] dealloc_complete_entry_id
);

  // ----------tracker reorder basic checks----------
  br_tracker_reorder_basic_fpv_monitor #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth)
  ) fv_checker (
      .clk,
      .rst,
      .alloc_ready,
      .alloc_valid,
      .alloc_entry_id,
      .dealloc_valid,
      .dealloc_entry_id,
      .dealloc_complete_ready,
      .dealloc_complete_valid,
      .dealloc_complete_entry_id
  );

endmodule : br_tracker_reorder_fpv_monitor

bind br_tracker_reorder br_tracker_reorder_fpv_monitor #(
    .NumEntries(NumEntries),
    .EntryIdWidth(EntryIdWidth),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
