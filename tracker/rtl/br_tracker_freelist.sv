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
// If there are multiple allocation ports and fewer free entries than ports,
// the freelist will fairly distribute free entries to the allocation ports
// that are ready to accept them using a round-robin arbitration scheme.
// This implies some behavior of alloc_valid/alloc_ready that is different
// from a typical ready/valid interface.
//
// 1. alloc_valid depends combinationally on the corresponding alloc_ready.
//    i.e. alloc_valid[i] can only be asserted if alloc_ready[i] is asserted.
// 2. alloc_valid is not stable. If a higher priority allocation port asserts alloc_ready,
//    the alloc_valid for a lower priority port may be revoked.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_tracker_freelist #(
    // Number of entries in the freelist. Must be greater than NumAllocPorts.
    parameter int NumEntries = 2,
    // Number of allocation ports. Must be at least 1.
    parameter int NumAllocPorts = 1,
    // Number of deallocation ports. Must be at least 1.
    parameter int NumDeallocPorts = 1,
    // If 1, then assert there are no dealloc_valid bits asserted at the end of the test.
    // It is expected that alloc_valid could be 1 at end of the test because it's
    // a natural idle condition for this design.
    parameter bit EnableAssertFinalNotDeallocValid = 1,

    localparam int EntryIdWidth = $clog2(NumEntries),
    localparam int DeallocCountWidth = $clog2(NumDeallocPorts + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic [NumAllocPorts-1:0] alloc_ready,
    // alloc valid and entry ID are not guaranteed to be stable
    // If there are fewer free entries than allocation ports,
    // alloc_valid may be revoked if one of the alloc ports of
    // higher priority is popped.
    output logic [NumAllocPorts-1:0] alloc_valid,
    output logic [NumAllocPorts-1:0][EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input  logic [  NumDeallocPorts-1:0]                   dealloc_valid,
    input  logic [  NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id,
    // Number of deallocations that have been performed.
    // This count will be nonzero to indicate that a given number of
    // entries will be available for allocation again.
    output logic [DeallocCountWidth-1:0]                   dealloc_count
);
  // Integration Assertions

  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > NumAllocPorts)
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
  logic [NumAllocPorts-1:0] push_entry_id_valid;
  logic [NumAllocPorts-1:0][EntryIdWidth-1:0] push_entry_id;
  logic [NumAllocPorts-1:0][NumEntries-1:0] push_entry_id_onehot;

  br_enc_priority_encoder #(
      .NumResults(NumAllocPorts),
      .NumRequesters(NumEntries)
  ) br_enc_priority_encoder_free_entries (
      .clk,
      .rst,
      .in (unstaged_free_entries),
      .out(push_entry_id_onehot)
  );

  for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_push_entry_id
    // Encode the free entries to binary
    br_enc_onehot2bin #(
        .NumValues(NumEntries)
    ) br_enc_onehot2bin_push_entry_id (
        .clk,
        .rst,
        .in(push_entry_id_onehot[i]),
        .out_valid(push_entry_id_valid[i]),
        .out(push_entry_id[i])
    );
  end

  if (NumAllocPorts == 1) begin : gen_single_alloc_port
    logic push_ready;

    // Staging buffer
    br_flow_reg_fwd #(
        .Width(EntryIdWidth),
        .EnableAssertPushValidStability(1),
        // Since the entry ID is coming from a priority encoder,
        // it could be unstable if a higher priority entry is deallocated.
        .EnableAssertPushDataStability(0),
        // Expect that alloc_valid can be 1 at end of test (or when idle, in general)
        .EnableAssertFinalNotValid(0)
    ) br_flow_reg_fwd (
        .clk,
        .rst,
        .push_valid(push_entry_id_valid),
        .push_ready(push_ready),
        .push_data (push_entry_id),
        .pop_valid (alloc_valid),
        .pop_ready (alloc_ready),
        .pop_data  (alloc_entry_id)
    );

    // Free entry vector is updated when a push or deallocation happens.
    assign unstaged_free_entries_le = (push_entry_id_valid[0] && push_ready) || (|dealloc_valid);
    assign unstaged_free_entries_clear = push_ready ? push_entry_id_onehot : '0;
  end else begin : gen_multi_alloc_ports
    localparam int StagedCountWidth = $clog2(NumAllocPorts + 1);
    localparam int PortIdWidth = $clog2(NumAllocPorts);

    logic [NumAllocPorts-1:0][NumAllocPorts-1:0] alloc_select;
    logic [NumAllocPorts-1:0][NumAllocPorts-1:0] alloc_select_transposed;
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] staged_entry_ids;
    logic [StagedCountWidth-1:0] staged_count;
    logic [StagedCountWidth-1:0] allocated;

    // Fairly allocate the available staged entries to the allocation ports that
    // are ready.
    br_arb_multi_rr #(
        .NumRequesters(NumAllocPorts),
        .MaxGrantPerCycle(NumAllocPorts)
    ) br_arb_multi_rr_staged_entry_select (
        .clk,
        .rst,
        .enable_priority_update(1'b1),
        .request(alloc_ready),
        .grant(alloc_valid),
        .grant_ordered(alloc_select),
        .grant_allowed(staged_count),
        .grant_count(allocated)
    );

    for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_alloc_entry_id
      // Grant ordered is buffer entry by alloc port
      // We want alloc port by buffer entry, so we need to transpose
      for (genvar j = 0; j < NumAllocPorts; j++) begin : gen_alloc_select_transposed
        assign alloc_select_transposed[i][j] = alloc_select[j][i];
      end

      br_mux_onehot #(
          .NumSymbolsIn(NumAllocPorts),
          .SymbolWidth (EntryIdWidth)
      ) br_mux_onehot_alloc_entry_id (
          .select(alloc_select_transposed[i]),
          .in(staged_entry_ids),
          .out(alloc_entry_id[i])
      );
    end

    // Staged entry IDs update
    // Shift the entries down by the number that were allocated.
    // If there are free slots, fill them from the unstaged free entries.

    // Shift down the existing staged entries by the number that were allocated.
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] staged_entry_ids_shifted;
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] staged_entry_ids_shifted_qual;
    // Only used in assertions
    // ri lint_check_waive NOT_READ
    logic staged_entry_ids_shifted_valid;
    logic [PortIdWidth-1:0] staged_entry_ids_shift;
    logic [StagedCountWidth-1:0] staged_count_after_alloc;
    logic all_allocated;

    assign staged_count_after_alloc = staged_count - allocated;
    assign all_allocated = &(alloc_valid & alloc_ready);
    assign staged_entry_ids_shift = PortIdWidth'(allocated);
    assign staged_entry_ids_shifted_qual = (!all_allocated) ? staged_entry_ids_shifted : '0;

    br_shift_right #(
        .NumSymbols (NumAllocPorts),
        .MaxShift   (NumAllocPorts-1),
        .SymbolWidth(EntryIdWidth)
    ) br_shift_right_staged_entry_ids (
        .in(staged_entry_ids),
        .shift(staged_entry_ids_shift),
        .fill('0),
        .out_valid(staged_entry_ids_shifted_valid),
        .out(staged_entry_ids_shifted)
    );

    `BR_ASSERT_IMPL(staged_entry_ids_shifted_valid_a,
                    !all_allocated |-> staged_entry_ids_shifted_valid)

    // Shift the push entry IDs up to the first staged entry slot that won't
    // be filled by a previously staged entry.
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] push_entry_id_shifted;
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] push_entry_id_shifted_qual;
    logic [PortIdWidth-1:0] push_entry_id_shift;
    logic [StagedCountWidth-1:0] push_count;
    logic can_push;
    // Only used in assertions
    // ri lint_check_waive NOT_READ
    logic push_entry_id_shifted_valid;

    assign can_push = (staged_count_after_alloc != NumAllocPorts);
    assign push_entry_id_shift = PortIdWidth'(staged_count_after_alloc);
    assign push_entry_id_shifted_qual = can_push ? push_entry_id_shifted : '0;

    br_shift_left #(
        .NumSymbols (NumAllocPorts),
        .MaxShift   (NumAllocPorts-1),
        .SymbolWidth(EntryIdWidth)
    ) br_shift_left_push_entry_id (
        .in(push_entry_id),
        .shift(push_entry_id_shift),
        .fill('0),
        .out_valid(push_entry_id_shifted_valid),
        .out(push_entry_id_shifted)
    );

    `BR_ASSERT_IMPL(push_entry_id_shifted_valid_a, can_push |-> push_entry_id_shifted_valid)

    br_enc_countones #(
        .Width(NumAllocPorts)
    ) br_enc_countones_push_count (
        .in(push_entry_id_valid),
        .count(push_count)
    );

    // Update the staged count and entry IDs.
    logic [StagedCountWidth:0] staged_count_next_ext;
    logic [StagedCountWidth-1:0] staged_count_next;
    logic [StagedCountWidth-1:0] push_count_qual;
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] staged_entry_ids_next;
    logic staged_entry_ids_update;

    assign staged_count_next_ext = staged_count_after_alloc + push_count;

    always_comb begin
      if (staged_count_next_ext > NumAllocPorts) begin
        staged_count_next = NumAllocPorts;
        push_count_qual   = NumAllocPorts - staged_count_after_alloc;
      end else begin
        staged_count_next = StagedCountWidth'(staged_count_next_ext);
        push_count_qual   = push_count;
      end
    end

    assign staged_entry_ids_next   = staged_entry_ids_shifted_qual | push_entry_id_shifted_qual;
    assign staged_entry_ids_update = (allocated != '0) || (push_count_qual != '0);

    `BR_REGL(staged_entry_ids, staged_entry_ids_next, staged_entry_ids_update)
    `BR_REGL(staged_count, staged_count_next, staged_entry_ids_update)

    // Clear the unstaged free entries that are being pushed into the staged buffer.
    logic [NumAllocPorts-1:0] push_entry_id_ready;

    for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_push_entry_id_ready
      assign push_entry_id_ready[i] = (i < push_count_qual);
    end

    assign unstaged_free_entries_le = (can_push && (|push_entry_id_valid)) || (|dealloc_valid);
    always_comb begin
      unstaged_free_entries_clear = '0;
      for (int i = 0; i < NumAllocPorts; i++) begin : gen_unstaged_free_entries_clear
        if (push_entry_id_ready[i]) begin
          unstaged_free_entries_clear |= push_entry_id_onehot[i];
        end
      end
    end

    `BR_ASSERT_IMPL(staged_entry_ids_next_no_conflict_a,
                    (staged_entry_ids_shifted_qual & push_entry_id_shifted_qual) == '0)
  end

  // Deallocation Logic
  logic [NumDeallocPorts-1:0][NumEntries-1:0] dealloc_entry_id_onehot;

  for (genvar i = 0; i < NumDeallocPorts; i++) begin : gen_dealloc_entry_id_onehot
    br_enc_bin2onehot #(
        .NumValues(NumEntries),
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

  logic [DeallocCountWidth-1:0] dealloc_count_next;

  br_enc_countones #(
      .Width(NumDeallocPorts)
  ) br_enc_countones_dealloc_count (
      .in(dealloc_valid),
      .count(dealloc_count_next)
  );

  // Need to delay the dealloc count by a cycle
  // to match the delay to the allocation staging buffer.
  `BR_REG(dealloc_count, dealloc_count_next)

  // Implementation Assertions

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  logic [NumEntries-1:0] staged_entries, staged_entries_next;
  logic [NumEntries-1:0] all_entries;

  always_comb begin
    staged_entries_next = staged_entries;

    for (int i = 0; i < NumEntries; i++) begin : gen_staged_entries_next
      if (unstaged_free_entries_clear[i]) begin
        staged_entries_next[i] = 1'b1;
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

  if (NumAllocPorts == 1) begin : gen_single_alloc_stage_check
    `BR_ASSERT_IMPL(staged_entries_le_2_a, $countones(staged_entries) <= 2)
  end else begin : gen_multi_alloc_stage_check
    `BR_ASSERT_IMPL(staged_entries_le_num_ports_a, $countones(staged_entries) <= NumAllocPorts)
  end

  // Every entry must always be accounted for. It must either be allocated, in
  // the free vector, or in the staging buffer.
  `BR_ASSERT_IMPL(no_lost_entries_a, &all_entries)

  for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_per_port_checks
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

  `BR_ASSERT_IMPL(dealloc_count_a, (|dealloc_valid) |=> (dealloc_count == $past
                                   ($countones(dealloc_valid))))

  br_flow_checks_valid_data_impl #(
      .NumFlows(NumAllocPorts),
      .Width(EntryIdWidth),
      .EnableCoverBackpressure(1),
      .EnableAssertValidStability(NumAllocPorts == 1),
      .EnableAssertDataStability(NumAllocPorts == 1),
      // We expect alloc_valid can be 1 at the end of simulation (i.e., if all entries are free).
      // So don't do a BR_ASSERT_FINAL on it.
      .EnableAssertFinalNotValid(0)
  ) br_flow_checks_valid_data_impl_alloc (
      .clk,
      .rst,
      .valid(alloc_valid),
      .ready(alloc_ready),
      .data (alloc_entry_id)
  );

`endif
`endif

endmodule
