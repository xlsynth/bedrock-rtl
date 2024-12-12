// Copyright 2024 The Bedrock-RTL Authors
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
// Bedrock-RTL Free List Manager
//
// This module tracks a set of entries that can be dynamically allocated. It
// stages the next two entries to be allocated in a buffer and allows a single
// entry to be allocated every cycle. It supports deallocating one or more
// entries per cycle.
//
// The freelist manager ensures that once an entry is allocated, the same entry
// cannot be allocated again until it is deallocated.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_tracker_freelist #(
    parameter int NumEntries = 2,
    parameter int NumDeallocPorts = 1,

    localparam int EntryIdWidth = $clog2(NumEntries)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic alloc_ready,
    output logic alloc_valid,
    output logic [EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input logic [NumDeallocPorts-1:0]                   dealloc_valid,
    input logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id
);
  // Integration Assertions

  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries >= 2)
  `BR_ASSERT_STATIC(legal_num_dealloc_ports_a, NumDeallocPorts >= 1)


  `BR_ASSERT(alloc_in_range_a, alloc_valid |-> alloc_entry_id < NumEntries)

`ifdef BR_ASSERT_ON
  // Track the set of allocated entries and make sure we don't deallocate
  // an entry that has not been allocated.
  // ri lint_check_off IFDEF_CODE
  logic [NumEntries-1:0] allocated_entries;
  logic [NumEntries-1:0] allocated_entries_next;

  `BR_REG(allocated_entries, allocated_entries_next)

  always_comb begin
    allocated_entries_next = allocated_entries;

    if (alloc_valid && alloc_ready) begin
      // ri lint_check_waive VAR_INDEX_WRITE
      allocated_entries_next[alloc_entry_id] = 1'b1;
    end

    // ri lint_check_waive ONE_IF_CASE
    for (int i = 0; i < NumDeallocPorts; i++) begin
      if (dealloc_valid[i]) begin
        // ri lint_check_waive SEQ_COND_ASSIGNS VAR_INDEX_WRITE
        allocated_entries_next[dealloc_entry_id[i]] = 1'b0;
      end
    end
  end

  for (genvar i = 0; i < NumDeallocPorts; i++) begin : gen_dealloc_intg_asserts
    `BR_ASSERT(dealloc_in_range_a, dealloc_valid[i] |-> dealloc_entry_id[i] < NumEntries)
    `BR_ASSERT(no_dealloc_unallocated_a,
               dealloc_valid[i] |-> allocated_entries[dealloc_entry_id[i]])
  end
  // ri lint_check_on IFDEF_CODE
`endif

  // Implementation

  // Bit-vector tracks the free entries not staged in the output buffer.
  logic [NumEntries-1:0] unstaged_free_entries;
  logic [NumEntries-1:0] unstaged_free_entries_next;
  logic [NumEntries-1:0] unstaged_free_entries_init;
  logic [NumEntries-1:0] unstaged_free_entries_set;
  logic [NumEntries-1:0] unstaged_free_entries_clear;
  logic                  unstaged_free_entries_le;

  assign unstaged_free_entries_next =
      (unstaged_free_entries | unstaged_free_entries_set) & ~unstaged_free_entries_clear;
  assign unstaged_free_entries_init = {NumEntries{1'b1}};

  `BR_REGIL(unstaged_free_entries, unstaged_free_entries_next, unstaged_free_entries_le,
            unstaged_free_entries_init)

  // Push Interface of the output buffer.
  logic push_valid;
  logic push_ready;
  logic [EntryIdWidth-1:0] push_entry_id;
  logic [NumEntries-1:0] push_entry_id_onehot;

  // Pick the first free entry to push to the output buffer.
  br_enc_priority_encoder #(
      .NumRequesters(NumEntries)
  ) br_enc_priority_encoder_free_entries (
      .clk,
      .rst,
      .in (unstaged_free_entries),
      .out(push_entry_id_onehot)
  );

  // Encode the first free entry ID to binary
  br_enc_onehot2bin #(
      .NumValues(NumEntries)
  ) br_enc_onehot2bin_push_entry_id (
      .clk,
      .rst,
      .in(push_entry_id_onehot),
      .out_valid(),
      .out(push_entry_id)
  );

  assign push_valid = |unstaged_free_entries;

  // Free entry vector is updated when a push or deallocation happens.
  assign unstaged_free_entries_le = (push_valid && push_ready) || (|dealloc_valid);

  // Entry is cleared in vector when it is pushed to the output buffer.
  assign unstaged_free_entries_clear = (push_valid && push_ready) ? push_entry_id_onehot : '0;

  // Deallocation Logic
  logic [NumDeallocPorts-1:0][NumEntries-1:0] dealloc_entry_id_onehot;

  for (genvar i = 0; i < NumDeallocPorts; i++) begin : gen_dealloc_entry_id_onehot
    br_enc_bin2onehot #(
        .NumValues(NumEntries)
    ) br_enc_bin2onehot_dealloc_entry_id (
        .clk,
        .rst,
        .in_valid(dealloc_valid[i]),
        .in(dealloc_entry_id[i]),
        .out(dealloc_entry_id_onehot[i])
    );
  end

  // Entries are set in vector when they are deallocated.
  always_comb begin
    unstaged_free_entries_set = '0;

    for (int i = 0; i < NumDeallocPorts; i++) begin
      unstaged_free_entries_set |= dealloc_entry_id_onehot[i];
    end
  end

  // Staging buffer
  br_flow_reg_both #(
      .Width(EntryIdWidth),
      // Since the entry ID is coming from a priority encoder,
      // it could be unstable if a higher priority entry is deallocated.
      .EnableAssertPushDataStability(0)
  ) br_flow_reg_both (
      .clk,
      .rst,
      .push_valid,
      .push_ready,
      .push_data(push_entry_id),
      .pop_valid(alloc_valid),
      .pop_ready(alloc_ready),
      .pop_data (alloc_entry_id)
  );

  // Implementation Assertions

`ifdef BR_ASSERT_ON
  logic [NumEntries-1:0] staged_entries, staged_entries_next;
  logic [NumEntries-1:0] all_entries;

  always_comb begin
    staged_entries_next = staged_entries;

    if (push_valid && push_ready) begin
      // ri lint_check_waive VAR_INDEX_WRITE
      staged_entries_next[push_entry_id] = 1'b1;
    end

    // ri lint_check_waive ONE_IF_CASE
    if (alloc_valid && alloc_ready) begin
      // ri lint_check_waive SEQ_COND_ASSIGNS VAR_INDEX_WRITE
      staged_entries_next[alloc_entry_id] = 1'b0;
    end
  end

  `BR_REG(staged_entries, staged_entries_next)

  assign all_entries = staged_entries | unstaged_free_entries | allocated_entries;

  // Every entry must always be accounted for. It must either be allocated, in
  // the free vector, or in the staging buffer.
  `BR_ASSERT(no_lost_entries_a, &all_entries)
  // Ensure that we don't allocate the same entry twice without deallocating it.
  `BR_ASSERT(no_double_alloc_a, alloc_valid |-> !allocated_entries[alloc_entry_id])
`endif

endmodule
