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

`include "br_asserts.svh"
`include "br_unused.svh"

module br_tracker_reorder_buffer_ctrl_1r1w #(
    // Number of entries in the reorder buffer. Must be at least 1.
    parameter int NumEntries = 2,
    // Width of the entry ID. Must be at least $clog2(NumEntries).
    parameter int EntryIdWidth = $clog2(NumEntries),
    // Width of the data payload.
    parameter int DataWidth = 1,
    // Number of clock cycles for the RAM read latency.
    parameter int RamReadLatency = 1,
    // If 1, then assert unordered_resp_push_valid is low at the end of the test.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    localparam int MinEntryIdWidth = $clog2(NumEntries)
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

    // 1R1W RAM Interface
    output logic [MinEntryIdWidth-1:0] ram_wr_addr,
    output logic ram_wr_valid,
    output logic [DataWidth-1:0] ram_wr_data,
    output logic [MinEntryIdWidth-1:0] ram_rd_addr,
    output logic ram_rd_addr_valid,
    input logic [DataWidth-1:0] ram_rd_data,
    input logic ram_rd_data_valid
);

  `BR_ASSERT_STATIC(legal_entry_id_width_a, EntryIdWidth >= MinEntryIdWidth)

  localparam int StagingFifoDepth = RamReadLatency + 2;

  logic reordered_resp_pop_beat_int;
  logic reordered_resp_pop_valid_int;
  logic reordered_resp_pop_ready_int;
  logic [EntryIdWidth-1:0] reordered_resp_pop_entry_id_int;
  logic id_skid_fifo_pop_ready;
  logic id_skid_fifo_pop_valid;
  logic data_skid_fifo_pop_ready;
  logic data_skid_fifo_pop_valid;

  // Token FIFO to ensure there is enough space in the data_skid_fifo to land
  // data read from RAM.
  br_fifo_flops #(
      .Depth(StagingFifoDepth),
      .Width(1'b1)
  ) br_fifo_flops_id_skid (
      .clk,
      .rst,
      //
      .push_ready(reordered_resp_pop_ready_int),
      .push_valid(reordered_resp_pop_valid_int),
      .push_data(1'b0),
      //
      .pop_ready(id_skid_fifo_pop_ready),
      .pop_valid(id_skid_fifo_pop_valid),
      .pop_data(),
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

  br_fifo_flops #(
      .Depth(StagingFifoDepth),
      .Width(DataWidth),
      // This FIFO should never backpressure. The same-depth
      // br_fifo_flops_id_skid FIFO provides necessary flow control because it
      // is always popped at the same time, and is only pushed when a
      // corresponding entry in the id_skid_fifo has been pushed successfully.
      // Disabling this cover asserts that the data_skid_fifo will never
      // backpressure.
      .EnableCoverPushBackpressure(0)
  ) br_fifo_flops_data_skid (
      .clk,
      .rst,
      //
      .push_ready(),
      .push_valid(ram_rd_data_valid),
      .push_data(ram_rd_data),
      //
      .pop_ready(data_skid_fifo_pop_ready),
      .pop_valid(data_skid_fifo_pop_valid),
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
      .dealloc_complete_entry_id(reordered_resp_pop_entry_id_int)
  );

  br_flow_join #(
      .NumFlows(2)
  ) br_flow_join_combine_skid_fifos (
      .clk,
      .rst,
      //
      .push_ready({id_skid_fifo_pop_ready, data_skid_fifo_pop_ready}),
      .push_valid({id_skid_fifo_pop_valid, data_skid_fifo_pop_valid}),
      //
      .pop_ready (reordered_resp_pop_ready),
      .pop_valid (reordered_resp_pop_valid)
  );

  assign ram_wr_addr = unordered_resp_push_entry_id[MinEntryIdWidth-1:0];
  assign ram_wr_valid = unordered_resp_push_valid;
  assign ram_wr_data = unordered_resp_push_data;

  assign ram_rd_addr = reordered_resp_pop_entry_id_int[MinEntryIdWidth-1:0];
  assign ram_rd_addr_valid = reordered_resp_pop_beat_int;

  assign reordered_resp_pop_beat_int = reordered_resp_pop_valid_int && reordered_resp_pop_ready_int;

  if (EntryIdWidth > MinEntryIdWidth) begin : gen_unused_upper_entry_id_bits
    `BR_UNUSED_NAMED(unused_upper_entry_id_bits,
                     reordered_resp_pop_entry_id_int[EntryIdWidth-1:MinEntryIdWidth])
  end

endmodule
