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
//
// Bedrock-RTL 1R1W Reorder Buffer Controller
//
// Uses br_reorder_tracker to implement a reorder buffer. Tags are allocated
// from the allocate interface (i.e. for requests) and responses returned on the
// unordered_resp_push interface. The reordered responses are returned on the
// reordered_resp_pop interface. Data provided on the unordered_resp_push
// interface is stored in a 1R1W RAM using the unordered_resp_push_entry_id as
// the write address when the unordered_resp_push_valid is asserted. The
// reordered_resp_pop_entry_id is used as the read address to retrieve the data
// when the reordered_resp_pop_valid is asserted, returning the data payloads
// (and associated IDs) in the original allocation order.
//
// The free_entry_count and allocated_entry_count outputs provide the number of
// free and allocated entries in the reorder buffer, respectively. Note that these
// counts do not consider responses pending in the output buffer whose tags have
// been retired but have not been popped from the reordered_resp_pop interface.
// In order to check that there are no unhandled responses remaining, the
// allocated_entry_count should be zero and the reordered_resp_pop_valid should
// be low.

`include "br_asserts.svh"
`include "br_unused.svh"

module br_tracker_reorder_buffer_ctrl_1r1w #(
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
    output logic [EntryCountWidth-1:0] free_entry_count,
    output logic [EntryCountWidth-1:0] allocated_entry_count,

    // 1R1W RAM Interface
    output logic [MinEntryIdWidth-1:0] ram_wr_addr,
    output logic ram_wr_valid,
    output logic [DataWidth-1:0] ram_wr_data,
    output logic [MinEntryIdWidth-1:0] ram_rd_addr,
    output logic ram_rd_addr_valid,
    input logic [DataWidth-1:0] ram_rd_data,
    input logic ram_rd_data_valid
);

  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries >= 1)
  `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= MinEntryIdWidth)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(legal_ram_read_latency_a, RamReadLatency >= 0)

  localparam int StagingFifoDepth = RamReadLatency + 2;

  logic reordered_resp_pop_valid_int;
  logic reordered_resp_pop_ready_int;
  logic [EntryIdWidth-1:0] reordered_resp_pop_entry_id_int;
  logic [EntryIdWidth-1:0] ram_rd_addr_int;

  // Credit sender ensures that we don't send read request until there is
  // space in the staging buffer.
  localparam int CreditWidth = $clog2(StagingFifoDepth + 1);
  logic [CreditWidth-1:0] credit_sender_initial;
  logic [CreditWidth-1:0] credit_sender_withhold;
  logic credit_sender_in_reset;
  logic [CreditWidth-1:0] credit_receiver_initial;
  logic [CreditWidth-1:0] credit_receiver_withhold;
  logic credit_receiver_in_reset;
  logic ram_rd_data_credit;

  assign credit_sender_initial = '0;
  assign credit_sender_withhold = '0;
  assign credit_receiver_initial = StagingFifoDepth;
  assign credit_receiver_withhold = '0;

  br_credit_sender #(
      .MaxCredit(StagingFifoDepth),
      .Width(EntryIdWidth)
  ) br_credit_sender_ram_rd_addr (
      .clk,
      .rst,
      .push_valid(reordered_resp_pop_valid_int),
      .push_ready(reordered_resp_pop_ready_int),
      .push_data(reordered_resp_pop_entry_id_int),
      .pop_sender_in_reset(credit_sender_in_reset),
      .pop_receiver_in_reset(credit_receiver_in_reset),
      .pop_credit(ram_rd_data_credit),
      .pop_valid(ram_rd_addr_valid),
      .pop_data(ram_rd_addr_int),

      .credit_initial(credit_sender_initial),
      .credit_withhold(credit_sender_withhold),
      .credit_count(),
      .credit_available()
  );

  assign ram_rd_addr = ram_rd_addr_int[MinEntryIdWidth-1:0];

  br_fifo_flops_push_credit #(
      .Depth(StagingFifoDepth),
      .Width(DataWidth),
      // This is needed because the FIFO does not support bypass
      // of credit to valid, but the credit sender does this.
      // TODO(zhemao): Remove this once this limitation is removed.
      .RegisterPushOutputs(1),
      .RegisterPopOutputs(RegisterPopOutputs)
  ) br_fifo_flops_data_skid (
      .clk,
      .rst,
      //
      .push_credit_stall(1'b0),
      .push_sender_in_reset(credit_sender_in_reset),
      .push_receiver_in_reset(credit_receiver_in_reset),
      .push_credit(ram_rd_data_credit),
      .push_valid(ram_rd_data_valid),
      .push_data(ram_rd_data),
      .credit_initial_push(credit_receiver_initial),
      .credit_withhold_push(credit_receiver_withhold),
      .credit_count_push(),
      .credit_available_push(),
      //
      .pop_ready(reordered_resp_pop_ready),
      .pop_valid(reordered_resp_pop_valid),
      .pop_data(reordered_resp_pop_data),
      //
      .full(),
      .full_next(),
      .slots(),
      .slots_next(),
      //
      .empty(),
      .empty_next(),
      .items(),
      .items_next()
  );

  br_tracker_reorder #(
      .NumEntries(NumEntries),
      .EntryIdWidth(EntryIdWidth),
      .EnableAssertFinalNotDeallocValid(EnableAssertFinalNotDeallocValid)
  ) br_tracker_reorder_inst (
      .clk,
      .rst,
      //
      .alloc_ready,
      .alloc_valid,
      .alloc_entry_id,
      //
      .dealloc_valid(unordered_resp_push_valid),
      .dealloc_entry_id(unordered_resp_push_entry_id),
      //
      .dealloc_complete_ready(reordered_resp_pop_ready_int),
      .dealloc_complete_valid(reordered_resp_pop_valid_int),
      .dealloc_complete_entry_id(reordered_resp_pop_entry_id_int),
      //
      .free_entry_count,
      .allocated_entry_count
  );

  assign ram_wr_addr  = unordered_resp_push_entry_id[MinEntryIdWidth-1:0];
  assign ram_wr_valid = unordered_resp_push_valid;
  assign ram_wr_data  = unordered_resp_push_data;

  if (EntryIdWidth > MinEntryIdWidth) begin : gen_unused_upper_entry_id_bits
    `BR_UNUSED_NAMED(unused_upper_entry_id_bits, ram_rd_addr_int[EntryIdWidth-1:MinEntryIdWidth])
  end

endmodule
