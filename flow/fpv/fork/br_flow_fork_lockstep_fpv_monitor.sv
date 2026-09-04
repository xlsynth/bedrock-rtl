// SPDX-License-Identifier: Apache-2.0

// FPV testplan: br_flow_fork_lockstep
//
// Design specification:
// - Control-only, combinational 1-to-NumFlows fork with no storage or datapath.
// - All downstream pop_ready bits must be equal.
// - Replicate push_valid to every pop_valid bit and return pop_ready[0] on
//   push_ready. Every downstream transfer coincides with the upstream transfer.
// - clk and synchronous active-high rst serve assertions only; reset does not
//   clear, gate, or register the flow-control outputs.
//
// Input assumptions (all expressed using primary inputs):
// - pop_ready_lockstep_a: pop_ready == {NumFlows{pop_ready[0]}}.
// - push_valid_stable_a: when EnableAssertPushValidStability is enabled,
//   push_valid && !pop_ready[0] requires push_valid on the following cycle.
// - no_push_backpressure_a: when EnableAssertNoPushBackpressure is enabled,
//   push_valid implies pop_ready[0]. Do not constrain readiness while idle.
// - No readiness fairness is needed: progress is checked in the same cycle that
//   the source is valid and the sinks are ready. Permanent stalls remain legal
//   when backpressure is allowed.
//
// Output assertions:
// - pop_valid_a: every pop_valid bit equals push_valid, including idle cycles.
// - push_ready_a: push_ready equals pop_ready[0], independent of push_valid.
// - transfer_lockstep_a: for each flow, pop_valid[i] && pop_ready[i] equals
//   push_valid && push_ready (no partial, lost, duplicated, or spurious transfer).
// - pop_valid_stable_a: valid persists under backpressure when source-valid
//   stability is enabled.
// - no_pop_backpressure_a: no valid output is stalled in no-backpressure mode.
// - forward_progress_a: valid input with ready sinks transfers on every output
//   immediately; no eventual-ready assumption or liveness bound is required.
//
// Covers:
// - Idle with all sinks ready and idle with all sinks not ready.
// - All flows transfer together, then transfer again on the next cycle.
// - When EnableCoverPushBackpressure is enabled, sustained all-flow stall and
//   release of a stall into a simultaneous transfer.
// - When source stability is disabled and backpressure coverage is enabled,
//   withdraw push_valid while all sinks remain stalled.
//
// Parameter and proof boundaries:
// - Sweep NumFlows = 1, 2, 4, 5 and all four legal combinations of the three
//   backpressure/stability flags (16 configurations).
// - Exclude NumFlows < 1, stability enabled with backpressure coverage disabled,
//   and no-backpressure assertion enabled with backpressure coverage enabled.
// - EnableAssertFinalNotValid is forwarded; the standard FPV wrapper disables
//   simulation-only final checks. No payload ordering scoreboard is applicable.
// - Normal startup reset only; properties are disabled during reset.

`include "br_asserts.svh"
`include "br_registers.svh"

module br_flow_fork_lockstep_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic push_ready,
    input logic push_valid,

    // Pop-side interfaces
    input logic [NumFlows-1:0] pop_ready,
    input logic [NumFlows-1:0] pop_valid
);

  // ----------Input assumptions----------
  // The fork forwards one ready bit, so every sink must agree with that bit.
  `BR_ASSUME(pop_ready_lockstep_a, pop_ready == {NumFlows{pop_ready[0]}})

  if (EnableAssertPushValidStability) begin : gen_push_valid_stability
    // A stalled source retains valid when this interface contract is enabled.
    `BR_ASSUME(push_valid_stable_a, push_valid && !pop_ready[0] |=> push_valid)
  end

  if (EnableAssertNoPushBackpressure) begin : gen_no_push_backpressure
    // No-backpressure mode permits a valid source only when all sinks are ready.
    `BR_ASSUME(no_push_backpressure_a, push_valid |-> pop_ready[0])
  end

  // ----------Transfer observations----------
  logic fv_push_transfer;
  logic [NumFlows-1:0] fv_pop_transfer;
  logic fv_stall;

  assign fv_push_transfer = push_valid && push_ready;
  assign fv_pop_transfer = pop_valid & pop_ready;
  assign fv_stall = push_valid && !push_ready && (&pop_valid) && (pop_ready == '0);

  // ----------Output assertions----------
  // Readiness propagates even during idle cycles; valid cannot gate it.
  `BR_ASSERT(push_ready_a, push_ready == pop_ready[0])

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    // Every output follows the source valid, including when the source is idle.
    `BR_ASSERT(pop_valid_a, pop_valid[i] == push_valid)

    // Each sink accepts exactly when the source does, forbidding partial transfers.
    `BR_ASSERT(transfer_lockstep_a, fv_pop_transfer[i] == fv_push_transfer)

    if (EnableAssertPushValidStability) begin : gen_pop_valid_stability
      // The source hold contract must propagate to each backpressured output.
      `BR_ASSERT(pop_valid_stable_a, pop_valid[i] && !pop_ready[i] |=> pop_valid[i])
    end

    if (EnableAssertNoPushBackpressure) begin : gen_no_pop_backpressure
      // A valid output cannot be stalled under the no-backpressure input contract.
      `BR_ASSERT(no_pop_backpressure_a, pop_valid[i] |-> pop_ready[i])
    end
  end

  // Available input and ready sinks must transfer together without adding latency.
  `BR_ASSERT(forward_progress_a,
             push_valid && (&pop_ready) |-> fv_push_transfer && (&fv_pop_transfer))

  // ----------Covers----------
  // Readiness may remain low while the source is idle in every parameter mode.
  `BR_COVER(idle_not_ready_c, !push_valid && (pop_valid == '0) && !push_ready && (pop_ready == '0))

  // An idle source does not prevent readiness from reaching the push interface.
  `BR_COVER(idle_ready_c, !push_valid && (pop_valid == '0) && push_ready && (&pop_ready))

  // Exercise a transfer accepted by the source and every sink in the same cycle.
  `BR_COVER(all_flows_transfer_c, fv_push_transfer && (&fv_pop_transfer))

  // Exercise full throughput without inserting a bubble between transfers.
  `BR_COVER(consecutive_transfers_c,
            fv_push_transfer && (&fv_pop_transfer) ##1 fv_push_transfer && (&fv_pop_transfer))

  if (EnableCoverPushBackpressure) begin : gen_backpressure_covers
    // All outputs may remain stalled together for more than one cycle.
    `BR_COVER(sustained_stall_c, fv_stall ##1 fv_stall)

    // A sustained stall can release directly into a simultaneous transfer.
    `BR_COVER(stall_then_transfer_c,
              fv_stall ##1 fv_stall ##1 fv_push_transfer && (&fv_pop_transfer))

    if (!EnableAssertPushValidStability) begin : gen_unstable_valid_cover
      // Without the source hold contract, valid may withdraw while sinks stay stalled.
      `BR_COVER(valid_withdrawal_c,
                fv_stall ##1
               !push_valid && (pop_valid == '0) && !push_ready && (pop_ready == '0))
    end
  end

endmodule : br_flow_fork_lockstep_fpv_monitor

bind br_flow_fork_lockstep br_flow_fork_lockstep_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
) monitor (.*);
