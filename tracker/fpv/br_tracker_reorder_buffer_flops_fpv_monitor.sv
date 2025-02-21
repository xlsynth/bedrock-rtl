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
    // If 1, then assert unordered_resp_push_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    input logic alloc_valid,
    input logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Request Interface
    input logic unordered_resp_push_valid,
    input logic [EntryIdWidth-1:0] unordered_resp_push_entry_id,
    input logic [DataWidth-1:0] unordered_resp_push_data,

    // Deallocation Complete Interface
    input logic reordered_resp_pop_ready,
    input logic reordered_resp_pop_valid,
    input logic [EntryIdWidth-1:0] reordered_resp_pop_entry_id,
    input logic [DataWidth-1:0] reordered_resp_pop_data
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
      .dealloc_valid(unordered_resp_push_valid),
      .dealloc_entry_id(unordered_resp_push_entry_id),
      .dealloc_complete_ready(reordered_resp_pop_ready),
      .dealloc_complete_valid(reordered_resp_pop_valid),
      .dealloc_complete_entry_id(reordered_resp_pop_entry_id)
  );

  // ----------FV assertions----------
  `BR_ASSERT(dealloc_complete_data_stable_a,
             reordered_resp_pop_valid && !reordered_resp_pop_ready |=>
             $stable(reordered_resp_pop_data))

  // pick random entry to check data integrity
  logic [EntryIdWidth-1:0] fv_entry_id;
  logic [DataWidth-1:0] fv_data;

  `BR_ASSUME(fv_entry_id_a, $stable(fv_entry_id) && fv_entry_id < NumEntries)
  `BR_REGL(fv_data, unordered_resp_push_data,
           unordered_resp_push_valid && (unordered_resp_push_entry_id == fv_entry_id))

  // alloc and dealloc_complete payload are in order
  `BR_ASSERT(data_in_order_check_a,
             reordered_resp_pop_valid && (reordered_resp_pop_entry_id == fv_entry_id) |->
             reordered_resp_pop_data == fv_data)

endmodule : br_tracker_reorder_buffer_flops_fpv_monitor

bind br_tracker_reorder_buffer_flops br_tracker_reorder_buffer_flops_fpv_monitor #(
    .NumEntries(NumEntries),
    .EntryIdWidth(EntryIdWidth),
    .DataWidth(DataWidth),
    .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
) monitor (.*);
