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
// entries will be assigned to the ports in fixed priority. That is, if there
// are N free entries where N < NumAllocPorts, then only alloc_valid[0] through
// alloc_valid[N-1] will be high. The alloc_valid will not be stable.
// If one of the higher priority ports is allocated and there are not enough
// free entries, entries will be shifted up from the lower priority ports.

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

    localparam int EntryIdWidth = $clog2(NumEntries)
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
    input logic [NumDeallocPorts-1:0]                   dealloc_valid,
    input logic [NumDeallocPorts-1:0][EntryIdWidth-1:0] dealloc_entry_id
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
    // If there are multiple allocation ports, we want a deterministic behavior
    // when the number of free entries is less than the number of allocation ports.
    // The ready/valid interface for each allocation port cannot be treated
    // independently, since we want alloc_valid[i] to be high so long as
    // there are more than i free entries. Because the remaining entries might all be
    // buffered already, we cannot guarantee this if we exclusively pull from the
    // unstaged free entries vector. The only way to guarantee this is to have the
    // buffer for the higher priority alloc ports steal from the lower priority
    // ports before pulling from the unstaged free entries vector.
    localparam int StagedCountWidth = $clog2(NumAllocPorts + 1);
    localparam int PortIdWidth = $clog2(NumAllocPorts);

    logic [StagedCountWidth-1:0] pushable_unstaged_count;
    logic [StagedCountWidth-1:0] staged_count;
    logic [StagedCountWidth-1:0] staged_count_next;
    logic [StagedCountWidth-1:0] staged_count_pop;
    logic [StagedCountWidth-1:0] staged_count_push;
    logic [StagedCountWidth-1:0] staged_count_after_pop;
    logic [StagedCountWidth-1:0] staged_slots_after_pop;
    logic [NumAllocPorts-1:0] alloc_beat;
    logic [NumAllocPorts-1:0] alloc_valid_next;
    logic [NumAllocPorts-1:0][EntryIdWidth-1:0] alloc_entry_id_next;
    logic [NumAllocPorts-1:0] alloc_update;

    assign alloc_beat = alloc_valid & alloc_ready;

    br_enc_countones #(
        .Width(NumAllocPorts)
    ) br_enc_countones_staged_count_pop (
        .in(alloc_beat),
        .count(staged_count_pop)
    );

    br_enc_countones #(
        .Width(NumAllocPorts)
    ) br_enc_countones_pushable_unstaged_count (
        .in(push_entry_id_valid),
        .count(pushable_unstaged_count)
    );

    assign staged_count_after_pop = staged_count - staged_count_pop;
    assign staged_slots_after_pop = NumAllocPorts - staged_count_after_pop;
    assign staged_count_push =
        (pushable_unstaged_count < staged_slots_after_pop) ?
        pushable_unstaged_count : staged_slots_after_pop;
    assign staged_count_next = staged_count_after_pop + staged_count_push;
    `BR_REGL(staged_count, staged_count_next, (unstaged_free_entries_le || (|alloc_beat)))

    logic [NumAllocPorts-1:0] push_entry_id_ready;

    for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_push_entry_id_ready
      assign push_entry_id_ready[i] = i < staged_count_push;
    end

    assign unstaged_free_entries_le = (staged_count_push != '0) || (|dealloc_valid);
    // If we are pushing N entries to the buffer,
    // Clear the first N entries in the unstaged free entries vector.
    always_comb begin
      unstaged_free_entries_clear = '0;
      for (int i = 0; i < NumAllocPorts; i++) begin
        if (push_entry_id_ready[i]) begin
          unstaged_free_entries_clear |= push_entry_id_onehot[i];
        end
      end
    end

    `BR_REG(alloc_valid, alloc_valid_next)

    for (genvar i = 0; i < NumAllocPorts; i++) begin : gen_alloc_entry_id
      logic can_steal;
      logic [EntryIdWidth-1:0] stolen_entry_id;

      if (i < NumAllocPorts - 2) begin : gen_multi_entry_stealing
        localparam int NumLowerPorts = NumAllocPorts - i - 1;

        logic [NumLowerPorts-1:0] stealable;
        logic [NumLowerPorts-1:0] stealable_onehot;

        // Steal entries from lower priority ports.
        for (genvar j = 0; j < NumLowerPorts; j++) begin : gen_stealable
          assign stealable[j] = alloc_valid[i+1+j] && !alloc_ready[i+1+j];
        end

        br_enc_priority_encoder #(
            .NumRequesters(NumLowerPorts)
        ) br_enc_priority_encoder (
            .clk,
            .rst,
            .in (stealable),
            .out(stealable_onehot)
        );

        br_mux_onehot #(
            .NumSymbolsIn(NumLowerPorts),
            .SymbolWidth (EntryIdWidth)
        ) br_mux_onehot_stolen_entry_id (
            .select(stealable_onehot),
            .in(alloc_entry_id[NumAllocPorts-1:i+1]),
            .out(stolen_entry_id)
        );
        assign can_steal = |stealable;
      end else if (i == (NumAllocPorts - 2)) begin : gen_single_entry_stealing
        // The second to last port can only steal from the last port.
        assign can_steal = alloc_valid[NumAllocPorts-1] && !alloc_ready[NumAllocPorts-1];
        assign stolen_entry_id = alloc_entry_id[NumAllocPorts-1];
      end else begin : gen_no_stealing
        // The MSB port has no lower priority ports to steal from.
        assign can_steal = 1'b0;
        assign stolen_entry_id = '0;
      end

      logic [ PortIdWidth-1:0] push_entry_select;
      logic [EntryIdWidth-1:0] selected_entry_id;

      // staged_entries_after_pop is the number of entries valid
      // on this cycle that will still be valid on the next cycle.
      // All entries with index >= staged_entries_after_pop will
      // need to pull entries from the unstaged free entries vector.
      assign push_entry_select = i - PortIdWidth'(staged_count_after_pop);

      br_mux_bin #(
          .NumSymbolsIn(NumAllocPorts),
          .SymbolWidth(EntryIdWidth),
          .EnableSelectInRange(0)
      ) br_mux_bin_alloc_entry_id (
          .select(push_entry_select),
          .in(push_entry_id),
          .out(selected_entry_id),
          .out_valid()
      );

      assign alloc_valid_next[i] = (staged_count_next > i);
      // We need to update if the currently held entry will not be valid
      // in the next cycle. That can happen if
      // 1. It's not valid now
      // 2. It's being popped
      // 3. It's being stolen by a higher priority port
      if (i == 0) begin : gen_alloc_update_0
        assign alloc_update[i] = alloc_valid_next[i] && (!alloc_valid[i] || alloc_ready[i]);
      end else begin : gen_alloc_update_gt0
        assign alloc_update[i] = alloc_valid_next[i] && (
            !alloc_valid[i] || alloc_ready[i] || (|alloc_update[i-1:0]));
      end

      assign alloc_entry_id_next[i] = can_steal ? stolen_entry_id : selected_entry_id;
      `BR_REGL(alloc_entry_id[i], alloc_entry_id_next[i], alloc_update[i])
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

    if (i > 0) begin : gen_alloc_priority_check
      `BR_ASSERT_IMPL(alloc_priority_a, alloc_valid[i] |-> &alloc_valid[i-1:0])
    end

    // ri lint_check_waive LOOP_NOT_ENTERED
    for (genvar j = i + 1; j < NumAllocPorts; j++) begin : gen_no_double_alloc_comb_assert
      // Ensure that we don't allocate the same entry from two different ports.
      `BR_ASSERT_IMPL(
          no_double_alloc_comb_a,
          (alloc_valid[i] && alloc_valid[j]) |-> (alloc_entry_id[i] != alloc_entry_id[j]))
    end
  end

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
