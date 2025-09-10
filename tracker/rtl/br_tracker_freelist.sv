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
// allows multiple entries to be allocated per cycle and multiple entries to be
// deallocated per cycle.
//
// Allocations are presented through a multi-transfer interface.
// alloc_sendable indicates the number of allocations that can be sent on a
// cycle, and alloc_entry_id from 0 to alloc_sendable-1 will be valid.
// The user indicates how many allocated entries they will take using the
// alloc_receivable signal.
//
// There is a two cycle delay between an entry being deallocated and
// when it can be reallocated.
//
// The freelist manager ensures that once an entry is allocated, the same entry
// cannot be allocated again until it is deallocated.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_tracker_freelist #(
    // Number of entries in the freelist. Must be greater than NumAllocPerCycle.
    parameter int NumEntries = 2,
    // Number of allocations per cycle. Must be at least 1.
    parameter int NumAllocPerCycle = 1,
    // Number of deallocation ports. Must be at least 1.
    parameter int NumDeallocPorts = 1,
    // If 1, then register the alloc_sendable and alloc_entry_id outputs,
    // improving timing at the cost of an additional cycle of cut-through latency.
    // Note that if this is set to 0, the alloc_entry_id may be unstable
    parameter bit RegisterAllocOutputs = 1,
    // Multihot vector indicating which entries are preallocated out of reset.
    // E.g. PreallocatedEntries[0] = 1'b1 indicates that entry 0 is preallocated.
    parameter logic [NumEntries-1:0] PreallocatedEntries = '0,
    // If 1, bypass deallocated entries to allocated entries.
    parameter bit EnableBypass = 0,
    // Cut-through latency of the tracker.
    localparam int CutThroughLatency = RegisterAllocOutputs + (EnableBypass ? 0 : 1),
    // The delay between an entry being deallocated and when the deallocation
    // is indicated by dealloc_count.
    // If dealloc_count is being used to manage credit returns, this must be set
    // so that allocation is not attemped until (CutThroughLatency - DeallocCountDelay) cycles
    // after deallocation is indicated on dealloc_count,
    // where CutThroughLatency = RegisterAllocOutputs + (EnableBypass ? 0 : 1).
    // Must be >= 0 and <= CutThroughLatency.
    parameter int DeallocCountDelay = CutThroughLatency,
    // If 1, then assert there are no dealloc_valid bits asserted at the end of the test.
    // It is expected that alloc_valid could be 1 at end of the test because it's
    // a natural idle condition for this design.
    parameter bit EnableAssertFinalNotDeallocValid = 1,
    // If 1, then assert that the number of allocated entries is the same as the number of
    // preallocated entries at the end of the test.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertFinalAllocatedInitial = 1,

    localparam int EntryIdWidth = $clog2(NumEntries),
    localparam int DeallocCountWidth = $clog2(NumDeallocPorts + 1),
    localparam int AllocCountWidth = $clog2(NumAllocPerCycle + 1)
) (
    input logic clk,
    input logic rst,

    // Allocation Interface
    input logic [AllocCountWidth-1:0] alloc_receivable,
    output logic [AllocCountWidth-1:0] alloc_sendable,
    output logic [NumAllocPerCycle-1:0][EntryIdWidth-1:0] alloc_entry_id,

    // Deallocation Interface
    input  logic [  NumDeallocPorts-1:0]                   dealloc_valid,
    input  logic [  NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id,
    // Number of deallocations that have been performed.
    // This count will be nonzero to indicate that a given number of
    // entries will be available for allocation again.
    output logic [DeallocCountWidth-1:0]                   dealloc_count
);
  // Integration Assertions

  `BR_ASSERT_STATIC(legal_num_entries_a, NumEntries > NumAllocPerCycle)
  `BR_ASSERT_STATIC(legal_num_alloc_per_cycle_a, NumAllocPerCycle >= 1)
  `BR_ASSERT_STATIC(legal_num_dealloc_ports_a, NumDeallocPorts >= 1)
  `BR_ASSERT_STATIC(legal_dealloc_count_delay_a,
                    DeallocCountDelay >= 0 && DeallocCountDelay <= CutThroughLatency)

  // Okay to use a non-synthesizable function here since it's for parameter only.
  // ri lint_check_waive SYS_TF
  localparam int NumPreallocatedEntries = $countones(PreallocatedEntries);

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS
  // Track the set of allocated entries and make sure we don't deallocate
  // an entry that has not been allocated.
  logic [NumEntries-1:0] allocated_entries;
  logic [NumEntries-1:0] allocated_entries_next;
  logic [NumAllocPerCycle-1:0] alloc_valid;

  `BR_REGI(allocated_entries, allocated_entries_next, PreallocatedEntries)

  if (EnableAssertFinalAllocatedInitial) begin : gen_assert_final
    `BR_ASSERT_FINAL(final_allocated_initial_a, $countones(allocated_entries
                     ) == NumPreallocatedEntries)
  end

  for (genvar i = 0; i < NumAllocPerCycle; i++) begin : gen_alloc_valid
    assign alloc_valid[i] = alloc_sendable > i && alloc_receivable > i;
  end

  always_comb begin
    allocated_entries_next = allocated_entries;

    for (int i = 0; i < NumDeallocPorts; i++) begin
      if (dealloc_valid[i]) begin
        // ri lint_check_waive VAR_INDEX_WRITE
        allocated_entries_next[dealloc_entry_id[i]] = 1'b0;
      end
    end

    // Allocation takes preference over deallocation
    // i.e. if an entry is being simultaneously deallocated and allocated,
    // it is considered allocated, since this is a bypass from dealloc
    // to alloc.
    // ri lint_check_waive ONE_IF_CASE
    for (int i = 0; i < NumAllocPerCycle; i++) begin : gen_alloc_intg_asserts
      if (alloc_valid[i]) begin
        // ri lint_check_waive SEQ_COND_ASSIGNS VAR_INDEX_WRITE
        allocated_entries_next[alloc_entry_id[i]] = 1'b1;
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
  logic [NumEntries-1:0] unstaged_free_entries_post_set;
  logic                  unstaged_free_entries_le;

  assign unstaged_free_entries_post_set = unstaged_free_entries | unstaged_free_entries_set;
  assign unstaged_free_entries_next = unstaged_free_entries_post_set & ~unstaged_free_entries_clear;
  assign unstaged_free_entries_init = ~PreallocatedEntries;

  `BR_REGLI(unstaged_free_entries, unstaged_free_entries_next, unstaged_free_entries_le,
            unstaged_free_entries_init)

  // Push Interface of the output buffer.
  logic [NumEntries-1:0] priority_encoder_in;
  logic [NumAllocPerCycle-1:0] push_entry_id_valid;
  logic [NumAllocPerCycle-1:0][EntryIdWidth-1:0] push_entry_id;
  logic [NumAllocPerCycle-1:0][NumEntries-1:0] push_entry_id_onehot;

  if (EnableBypass) begin : gen_bypass_priority_encoder_in
    assign priority_encoder_in = unstaged_free_entries_post_set;
  end else begin : gen_non_bypass_priority_encoder_in
    assign priority_encoder_in = unstaged_free_entries;
  end

  // This is the maximum number of entries that can be unstaged on any given cycle.
  // It is the maximum of the following three numbers:
  // 1. The number of entries set after reset (NumEntries - NumPreallocatedEntries)
  // 2. The maximum number of entries that can be deallocated on a given cycle.
  // (minimum of NumDeallocPorts and NumEntries)
  // 3. The maximum number of entries that can be waiting to be staged at steady
  // state when alloc is backpressured. (NumEntries minus staging buffer size)
  localparam int PriorityEncoderMaxInHot = br_math::max2(
      NumEntries - NumPreallocatedEntries,
      br_math::max2(
          br_math::min2(
              NumDeallocPorts, NumEntries
          ),
          NumEntries - (RegisterAllocOutputs ? NumAllocPerCycle : 0))
  );

  br_enc_priority_encoder #(
      .NumResults(NumAllocPerCycle),
      .NumRequesters(NumEntries),
      .MaxInHot(PriorityEncoderMaxInHot)
  ) br_enc_priority_encoder_free_entries (
      .clk,
      .rst,
      .in (priority_encoder_in),
      .out(push_entry_id_onehot)
  );

  for (genvar i = 0; i < NumAllocPerCycle; i++) begin : gen_push_entry_id
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

  if (NumAllocPerCycle == 1) begin : gen_single_alloc_port
    logic push_ready;

    if (RegisterAllocOutputs) begin : gen_reg_alloc
      // Staging buffer
      br_flow_reg_fwd #(
          .Width(EntryIdWidth),
          .EnableAssertPushValidStability(1),
          // Since the entry ID is coming from a priority encoder,
          // it could be unstable if a higher priority entry is deallocated.
          // This can only happen if there are more than two entries.
          // If there are only two, only one entry can be unstaged when push_ready
          // is low.
          .EnableAssertPushDataStability(NumEntries <= 2),
          // Expect that alloc_valid can be 1 at end of test (or when idle, in general)
          .EnableAssertFinalNotValid(0)
      ) br_flow_reg_fwd (
          .clk,
          .rst,
          .push_valid(push_entry_id_valid[0]),
          .push_ready(push_ready),
          .push_data (push_entry_id[0]),
          .pop_valid (alloc_sendable),
          .pop_ready (alloc_receivable),
          .pop_data  (alloc_entry_id)
      );
    end else begin : gen_no_reg_alloc
      assign alloc_sendable = push_entry_id_valid[0];
      assign alloc_entry_id = push_entry_id[0];
      assign push_ready = alloc_receivable;
    end

    // Free entry vector is updated when a push or deallocation happens.
    assign unstaged_free_entries_le = (push_entry_id_valid[0] && push_ready) || (|dealloc_valid);
    assign unstaged_free_entries_clear = push_ready ? push_entry_id_onehot : '0;
  end else begin : gen_multi_alloc_ports
    logic [ AllocCountWidth-1:0] push_sendable;
    logic [ AllocCountWidth-1:0] push_receivable;
    logic [NumAllocPerCycle-1:0] push_receivable_decoded;

    br_enc_countones #(
        .Width(NumAllocPerCycle)
    ) br_enc_countones_push_sendable (
        .in(push_entry_id_valid),
        .count(push_sendable)
    );

    if (RegisterAllocOutputs) begin : gen_reg_alloc
      br_multi_xfer_reg_fwd #(
          .NumSymbols(NumAllocPerCycle),
          .SymbolWidth(EntryIdWidth),
          // Data can be unstable because deallocating a higher priority entry
          // can supersede an existing free entry.
          // This can only happen if there are more than NumAllocPerCycle + 1 entries.
          .EnableAssertPushDataStability(NumEntries <= NumAllocPerCycle + 1),
          // We expect unstaged_free_entries to be 1 at the end of the test.
          .EnableAssertFinalNotSendable(0)
      ) br_multi_xfer_reg_fwd (
          .clk,
          .rst,
          .push_sendable,
          .push_receivable,
          .push_data(push_entry_id),
          .pop_sendable(alloc_sendable),
          .pop_receivable(alloc_receivable),
          .pop_data(alloc_entry_id)
      );
    end else begin : gen_no_reg_alloc
      assign alloc_sendable  = push_sendable;
      assign alloc_entry_id  = push_entry_id;
      assign push_receivable = alloc_receivable;
    end

    // Free entry vector is updated when a push or deallocation happens.
    assign unstaged_free_entries_le =
        (|push_entry_id_valid && push_receivable > '0) || (|dealloc_valid);
    for (genvar i = 0; i < NumAllocPerCycle; i++) begin : gen_push_receivable_decoded
      assign push_receivable_decoded[i] = push_receivable > i;
    end
    always_comb begin
      unstaged_free_entries_clear = '0;
      for (int i = 0; i < NumAllocPerCycle; i++) begin
        if (push_receivable_decoded[i]) begin
          unstaged_free_entries_clear |= push_entry_id_onehot[i];
        end
      end
    end
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

  br_delay #(
      .NumStages(DeallocCountDelay),
      .Width(DeallocCountWidth)
  ) br_delay_dealloc_count (
      .clk,
      .rst,
      .in(dealloc_count_next),
      .out(dealloc_count),
      .out_stages()
  );

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
    for (int i = 0; i < NumAllocPerCycle; i++) begin : gen_staged_entries_next
      if (alloc_valid[i]) begin
        // ri lint_check_waive SEQ_COND_ASSIGNS VAR_INDEX_WRITE
        staged_entries_next[alloc_entry_id[i]] = 1'b0;
      end
    end
  end

  `BR_REG(staged_entries, staged_entries_next)

  assign all_entries = staged_entries | unstaged_free_entries | allocated_entries;

  `BR_ASSERT_IMPL(staged_entries_le_num_ports_a, $countones(staged_entries) <= NumAllocPerCycle)

  // Every entry must always be accounted for. It must either be allocated, in
  // the free vector, or in the staging buffer.
  `BR_ASSERT_IMPL(no_lost_entries_a, &all_entries)

  for (genvar i = 0; i < NumAllocPerCycle; i++) begin : gen_per_port_checks
    `BR_ASSERT_IMPL(alloc_in_range_a, (alloc_sendable > i) |-> alloc_entry_id[i] < NumEntries)
    if (EnableBypass && !RegisterAllocOutputs) begin : gen_zero_latency_dealloc_check
      logic [NumDeallocPorts-1:0] dealloc_match;
      for (genvar j = 0; j < NumDeallocPorts; j++) begin : gen_dealloc_match
        assign dealloc_match[j] = dealloc_valid[j] && dealloc_entry_id[j] == alloc_entry_id[i];
      end
      // Ensure that we don't allocate the same entry twice without deallocating it.
      `BR_ASSERT_IMPL(
          no_double_alloc_seq_a,
          (alloc_sendable > i) |-> (|dealloc_match) || !allocated_entries[alloc_entry_id[i]])
      `BR_COVER_IMPL(bypass_dealloc_c, (alloc_sendable > i) && (|dealloc_match))
    end else begin : gen_positive_latency_dealloc_check
      // Ensure that we don't allocate the same entry twice without deallocating it.
      `BR_ASSERT_IMPL(no_double_alloc_seq_a,
                      (alloc_sendable > i) |-> !allocated_entries[alloc_entry_id[i]])
    end

    // ri lint_check_waive LOOP_NOT_ENTERED
    for (genvar j = i + 1; j < NumAllocPerCycle; j++) begin : gen_no_double_alloc_comb_assert
      // Ensure that we don't allocate the same entry from two different ports.
      `BR_ASSERT_IMPL(no_double_alloc_comb_a,
                      (alloc_sendable > j) |-> (alloc_entry_id[i] != alloc_entry_id[j]))
    end
  end

  if (DeallocCountDelay > 0) begin : gen_dealloc_count_delay_check
    `BR_ASSERT_IMPL(dealloc_count_a,
                    (|dealloc_valid) |-> ##DeallocCountDelay(dealloc_count == $past(
                        $countones(dealloc_valid), DeallocCountDelay
                    )))
  end else begin : gen_dealloc_count_no_delay_check
    `BR_ASSERT_IMPL(dealloc_count_a,
                    (|dealloc_valid) |-> (dealloc_count == $countones(dealloc_valid)))
  end

  if (CutThroughLatency > 0) begin : gen_nonzero_cut_through_latency_check
    `BR_ASSERT_IMPL(cut_through_latency_a,
                    (|dealloc_valid) |-> ##CutThroughLatency(alloc_sendable != '0))
  end else begin : gen_zero_cut_through_latency_check
    `BR_ASSERT_IMPL(zero_cut_through_latency_a, (|dealloc_valid) |-> (alloc_sendable != '0))
  end

`endif
`endif

endmodule
