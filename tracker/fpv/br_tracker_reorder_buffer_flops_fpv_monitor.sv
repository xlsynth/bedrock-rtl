// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Reorder Buffer (Flops Storage)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_reorder_buffer_flops_fpv_monitor #(
    parameter int NumEntries = 2,
    parameter int EntryIdWidth = 1,
    parameter int DataWidth = 1,
    parameter bit RegisterPopOutputs = 0,
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
