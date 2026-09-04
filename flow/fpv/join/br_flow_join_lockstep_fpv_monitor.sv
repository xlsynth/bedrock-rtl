// SPDX-License-Identifier: Apache-2.0

// FPV testplan: br_flow_join_lockstep
//
// Design specification:
// - Control-only, combinational NumFlows-to-1 join with no storage or datapath.
// - All upstream push_valid bits must be equal.
// - Pass push_valid[0] to pop_valid and replicate pop_ready to every push_ready
//   bit. Every upstream transfer coincides with the downstream transfer.
// - clk and synchronous active-high rst serve assertions only; reset does not
//   clear, gate, or register the flow-control outputs.
//
// Input assumptions (all expressed using primary inputs):
// - push_valid_lockstep_a: push_valid == {NumFlows{push_valid[0]}}.
// - push_valid_stable_a: when EnableAssertPushValidStability is enabled,
//   push_valid[i] && !pop_ready requires push_valid[i] on the following cycle.
// - no_push_backpressure_a: when EnableAssertNoPushBackpressure is enabled,
//   push_valid[0] implies pop_ready. Do not constrain readiness while idle.
// - No readiness fairness is needed: progress is checked in the same cycle that
//   the sources are valid and the sink is ready. Permanent stalls remain legal
//   when backpressure is allowed.
//
// Output assertions:
// - pop_valid_a: pop_valid equals push_valid[0], including idle cycles.
// - push_ready_a: every push_ready bit equals pop_ready, independent of valid.
// - transfer_lockstep_a: for each flow, push_valid[i] && push_ready[i] equals
//   pop_valid && pop_ready (no partial, lost, duplicated, or spurious transfer).
// - pop_valid_stable_a: valid persists under backpressure when source-valid
//   stability is enabled.
// - no_pop_backpressure_a: the valid output is never stalled in
//   no-backpressure mode.
// - forward_progress_a: valid sources with a ready sink all transfer
//   immediately; no eventual-ready assumption or liveness bound is required.
//
// Covers:
// - All sources idle with the sink ready and with the sink not ready.
// - All sources transfer together, then transfer again on the next cycle.
// - When EnableCoverPushBackpressure is enabled, sustained all-source stall and
//   release of a stall into a simultaneous transfer.
// - When source stability is disabled and backpressure coverage is enabled,
//   withdraw all push_valid bits together while the sink remains stalled.
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

module br_flow_join_lockstep_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic clk,
    input logic rst,

    // Push-side interfaces
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,

    // Pop-side interface
    input logic pop_ready,
    input logic pop_valid
);

  // ----------FV assumptions----------
  // The upstream sources present their valid bits in lockstep.
  `BR_ASSUME(push_valid_lockstep_a, push_valid == {NumFlows{push_valid[0]}})

  if (EnableAssertPushValidStability) begin : gen_push_valid_stability
    for (genvar i = 0; i < NumFlows; i++) begin : gen_flow
      // A stalled source retains valid until it can transfer.
      `BR_ASSUME(push_valid_stable_a, push_valid[i] && !pop_ready |=> push_valid[i])
    end
  end

  if (EnableAssertNoPushBackpressure) begin : gen_no_push_backpressure
    // The sink is ready whenever the lockstep sources present a transfer.
    `BR_ASSUME(no_push_backpressure_a, push_valid[0] |-> pop_ready)
  end

  // ----------FV assertions----------
  // The joined valid follows the source valid even when the sink is stalled.
  `BR_ASSERT(pop_valid_a, pop_valid == push_valid[0])

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    // Every source receives the sink readiness, including when all sources are idle.
    `BR_ASSERT(push_ready_a, push_ready[i] == pop_ready)

    // Each source transfers exactly when the joined output transfers.
    `BR_ASSERT(transfer_lockstep_a, (push_valid[i] && push_ready[i]) == (pop_valid && pop_ready))

    // A valid source and ready sink complete the transfer in the current cycle.
    `BR_ASSERT(forward_progress_a, push_valid[i] && pop_ready |-> push_ready[i] && pop_valid)
  end

  if (EnableAssertPushValidStability) begin : gen_pop_valid_stability
    // The joined valid obeys the source stability contract while stalled.
    `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  end

  if (EnableAssertNoPushBackpressure) begin : gen_no_pop_backpressure
    // The no-backpressure source contract also prevents a stalled joined output.
    `BR_ASSERT(no_pop_backpressure_a, pop_valid |-> pop_ready)
  end

  // ----------FV covers----------
  // All sources can be idle while the sink is not ready.
  `BR_COVER(idle_not_ready_c, !(|push_valid) && !pop_ready)

  // All sources can be idle while the sink is ready.
  `BR_COVER(idle_ready_c, !(|push_valid) && pop_ready)

  // All sources and the joined output can transfer together.
  `BR_COVER(transfer_c, (&push_valid) && (&push_ready) && pop_valid && pop_ready)

  // The join can sustain a transfer on consecutive cycles without inserting a bubble.
  `BR_COVER(consecutive_transfers_c,
            ((&push_valid) && (&push_ready) && pop_valid && pop_ready) [* 2])

  if (EnableCoverPushBackpressure) begin : gen_backpressure_covers
    // All sources and the joined output can remain stalled for multiple cycles.
    `BR_COVER(sustained_stall_c, ((&push_valid) && !(|push_ready) && pop_valid && !pop_ready) [* 3])

    // A sustained stall can end with a simultaneous source and output transfer.
    `BR_COVER(stall_release_c,
              ((&push_valid) && !(|push_ready) && pop_valid && !pop_ready)[*3] ##1
              ((&push_valid) && (&push_ready) && pop_valid && pop_ready))

    if (!EnableAssertPushValidStability) begin : gen_valid_withdrawal
      // The relaxed source contract allows all valid bits to fall while still stalled.
      `BR_COVER(valid_withdrawal_c,
                ((&push_valid) && pop_valid && !pop_ready) ##1
                (!(|push_valid) && !pop_valid && !pop_ready))
    end
  end

endmodule : br_flow_join_lockstep_fpv_monitor

bind br_flow_join_lockstep br_flow_join_lockstep_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
) monitor (.*);
