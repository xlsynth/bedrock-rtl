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
// allows multiple entries to be allocated per cycle. For each allocation port,
// it stages the next two entries to be allocated in a buffer. It supports
// deallocating one or more entries per cycle.
//
// The freelist manager ensures that once an entry is allocated, the same entry
// cannot be allocated again until it is deallocated.
//
// Note that fairness of allocation when the freelist is low on entries
// is not guaranteed. If the freelist is almost empty, the allocation ports
// get freed entries in fixed priority with port 0 having highest priority
// and port NumAllocPorts-1 having lowest priority.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_tracker_freelist #(
    // Number of entries in the freelist. Must be greater than 2 X NumAllocPorts.
    parameter int NumEntries = 2,
    // Number of allocation ports. Must be at least 1.
    parameter int NumAllocPorts = 1,
    // Number of deallocation ports. Must be at least 1.
    parameter int NumDeallocPorts = 1,
    // If 1, then assert there are no dealloc_valid bits asserted at the end of the test.
    // It is expected that alloc_valid could be 1 at end of the test because it's
    // a natural idle condition for this design.
    parameter bit EnableAssertFinalNotDeallocValid = 1,

    localparam int EntryIdWidth = $clog2(NumEntries)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic [NumAllocPorts-1:0] alloc_ready,
    output logic [NumAllocPorts-1:0] alloc_valid,
    output logic [NumAllocPorts-1:0][EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input logic [NumDeallocPorts-1:0]                   dealloc_valid,
    input logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id
);
  // Integration Assertions

  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > (2 * NumAllocPorts))
  `BR_ASSERT_STATIC(legal_num_alloc_ports_a, NumAllocPorts >= 1)
  `BR_ASSERT_STATIC(legal_num_dealloc_ports_a, NumDeallocPorts >= 1)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  // Track the set of allocated entries and make sure we don't deallocate
  // an entry that has not been allocated.
  logic [NumEntries-1:0] allocated_entries;
  logic [NumEntries-1:0] allocated_entries_next;

  `BR_REG(allocated_entries, allocated_entries_next)

  always_comb begin
    allocated_entries_next = allocated_entries;

    for (int i = 0; i < NumAllocPorts; i++) begin : gen_alloc_intg_asserts
      if (alloc_valid[i] && alloc_ready[i]) begin
        // ri lint_check_waive VAR_INDEX_WRITE
        allocated_entries_next[alloc_entry_id[i]] = 1'b1;
      end
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
    `BR_ASSERT_INTG(dealloc_in_range_a, dealloc_valid[i] |-> dealloc_entry_id[i] < NumEntries)
    `BR_ASSERT_INTG(no_dealloc_unallocated_a,
                    dealloc_valid[i] |-> allocated_entries[dealloc_entry_id[i]])
  end
`endif
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

  `BR_REGLI(unstaged_free_entries, unstaged_free_entries_next, unstaged_free_entries_le,
            unstaged_free_entries_init)

  // Push Interface of the output buffer.
  logic [NumAllocPorts-1:0] push_valid;
  logic [NumAllocPorts-1:0] push_ready;
  logic [NumAllocPorts-1:0][EntryIdWidth-1:0] push_entry_id;
  logic [NumAllocPorts-1:0][NumEntries-1:0] push_entry_id_onehot;

  for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_alloc_port
    logic [NumEntries-1:0] masked_free_entries;

    always_comb begin
      // Start with all free entries unmasked
      masked_free_entries = unstaged_free_entries;

      // ri lint_check_waive LOOP_NOT_ENTERED
      for (int j = 0; j < i; j++) begin
        // If a higher priority buffer is ready, mask off the entry that it will
        // take.
        if (push_ready[j]) begin
          masked_free_entries &= ~push_entry_id_onehot[j];
        end
      end
    end

    assign push_valid[i] = |masked_free_entries;

    // Pick the first unmasked free entry to push to the output buffer.
    br_enc_priority_encoder #(
        .NumRequesters(NumEntries)
    ) br_enc_priority_encoder_free_entries (
        .clk,
        .rst,
        .in (masked_free_entries),
        .out(push_entry_id_onehot[i])
    );

    // Encode the first free entry ID to binary
    br_enc_onehot2bin #(
        .NumValues(NumEntries),
        .EnableAssertFinalNotValid(EnableAssertFinalNotDeallocValid)
    ) br_enc_onehot2bin_push_entry_id (
        .clk,
        .rst,
        .in(push_entry_id_onehot[i]),
        .out_valid(),
        .out(push_entry_id[i])
    );

    // Staging buffer
    br_flow_reg_both #(
        .Width(EntryIdWidth),
        // If there is more than one allocation port, we might revoke the valid
        // if the last unstaged entry was taken by another port.
        .EnableAssertPushValidStability(NumAllocPorts == 1),
        // Since the entry ID is coming from a priority encoder,
        // it could be unstable if a higher priority entry is deallocated.
        .EnableAssertPushDataStability(0),
        // Expect that alloc_valid can be 1 at end of test (or when idle, in general)
        .EnableAssertFinalNotValid(0)
    ) br_flow_reg_both (
        .clk,
        .rst,
        .push_valid(push_valid[i]),
        .push_ready(push_ready[i]),
        .push_data (push_entry_id[i]),
        .pop_valid (alloc_valid[i]),
        .pop_ready (alloc_ready[i]),
        .pop_data  (alloc_entry_id[i])
    );
  end

  // Free entry vector is updated when a push or deallocation happens.
  assign unstaged_free_entries_le = (|(push_valid & push_ready)) || (|dealloc_valid);

  // Entry is cleared in vector when it is pushed to the output buffer.
  always_comb begin
    unstaged_free_entries_clear = '0;

    for (int i = 0; i < NumAllocPorts; i++) begin : gen_unstaged_free_entries_clear
      if (push_valid[i] && push_ready[i]) begin
        unstaged_free_entries_clear |= push_entry_id_onehot[i];
      end
    end
  end

  // Deallocation Logic
  logic [NumDeallocPorts-1:0][NumEntries-1:0] dealloc_entry_id_onehot;

  for (genvar i = 0; i < NumDeallocPorts; i++) begin : gen_dealloc_entry_id_onehot
    br_enc_bin2onehot #(
        .NumValues(NumEntries)
        .EnableAssertFinalNotValid(EnableAssertFinalNotDeallocValid)
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

  // Implementation Assertions

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  logic [NumEntries-1:0] staged_entries, staged_entries_next;
  logic [NumEntries-1:0] all_entries;

  always_comb begin
    staged_entries_next = staged_entries;

    for (int i = 0; i < NumAllocPorts; i++) begin : gen_staged_entries_next
      if (push_valid[i] && push_ready[i]) begin
        // ri lint_check_waive VAR_INDEX_WRITE
        staged_entries_next[push_entry_id[i]] = 1'b1;
      end
    end

    // ri lint_check_waive ONE_IF_CASE
    for (int i = 0; i < NumAllocPorts; i++) begin : gen_staged_entries_next
      if (alloc_valid[i] && alloc_ready[i]) begin
        // ri lint_check_waive SEQ_COND_ASSIGNS VAR_INDEX_WRITE
        staged_entries_next[alloc_entry_id[i]] = 1'b0;
      end
    end
  end

  `BR_REG(staged_entries, staged_entries_next)

  assign all_entries = staged_entries | unstaged_free_entries | allocated_entries;

  // Every entry must always be accounted for. It must either be allocated, in
  // the free vector, or in the staging buffer.
  `BR_ASSERT_IMPL(no_lost_entries_a, &all_entries)

  for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_no_double_alloc_asserts
    `BR_ASSERT_IMPL(alloc_in_range_a, alloc_valid[i] |-> alloc_entry_id[i] < NumEntries)
    // Ensure that we don't allocate the same entry twice without deallocating it.
    `BR_ASSERT_IMPL(no_double_alloc_seq_a, alloc_valid[i] |-> !allocated_entries[alloc_entry_id[i]])

    // ri lint_check_waive LOOP_NOT_ENTERED
    for (genvar j = i + 1; j < NumAllocPorts; j++) begin : gen_no_double_alloc_comb_assert
      // Ensure that we don't allocate the same entry from two different ports.
      `BR_ASSERT_IMPL(
          no_double_alloc_comb_a,
          (alloc_valid[i] && alloc_valid[j]) |-> (alloc_entry_id[i] != alloc_entry_id[j]))
    end
  end
`endif
`endif

  // We expect alloc_valid can be 1 at the end of simulation (i.e., if all entries are free).
  // So don't do a BR_ASSERT_FINAL on it.

endmodule
