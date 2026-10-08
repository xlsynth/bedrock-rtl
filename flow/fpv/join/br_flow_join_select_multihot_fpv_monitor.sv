// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Join With Multihot Select
//
// Check the combinational join contract: all selected sources participate in
// each output transfer, unselected sources do not participate, and an empty
// selection cannot produce an output transfer. There is no datapath or storage.
// Source-valid stability and no-backpressure assumptions follow the configured
// input contract. Selection is unconstrained, including during stalls, so the
// output valid is intentionally allowed to change while backpressured. Progress
// is immediate once all selected sources are valid and the sink is ready; no
// fairness assumption is needed. Properties use the standard startup reset.

`include "br_asserts.svh"

module br_flow_join_select_multihot_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter bit AllowEmptySelect = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertFinalNotValid = 1,
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure
) (
    input logic clk,
    input logic rst,

    input logic [NumFlows-1:0] select_multihot,

    // Push-side interfaces
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,

    // Pop-side interface
    input logic pop_ready,
    input logic pop_valid_unstable
);

  // Reference handshake derived only from primary inputs.
  logic [NumFlows-1:0] valid_select;
  logic [NumFlows-1:0] expected_push_ready;
  logic all_valid;
  // Each bit identifies a source that is both valid and selected.
  assign valid_select = push_valid & select_multihot;
  // The join is valid only when every selected source is valid.
  assign all_valid = (valid_select != '0) && (valid_select == select_multihot);

  for (genvar i = 0; i < NumFlows; i++) begin : gen_ready_model
    // A source need not assert its own valid to observe ready.
    assign expected_push_ready[i] = pop_ready && select_multihot[i] &&
        ((valid_select | (NumFlows'(1) << i)) == select_multihot);
  end

  // ----------FV assumptions----------
  if (!AllowEmptySelect) begin : gen_nonempty_select
    `BR_ASSUME(select_nonempty_a, select_multihot != '0)
  end

  for (genvar i = 0; i < NumFlows; i++) begin : gen_input_contract
    if (EnableAssertPushValidStability) begin : gen_valid_stability
      `BR_ASSUME(push_valid_stable_a, push_valid[i] && !expected_push_ready[i] |=> push_valid[i])
    end
    if (EnableAssertNoPushBackpressure) begin : gen_no_backpressure
      `BR_ASSUME(no_push_backpressure_a, push_valid[i] |-> expected_push_ready[i])
    end
  end

  // ----------FV assertions----------
  `BR_ASSERT(pop_valid_a, pop_valid_unstable == all_valid)
  `BR_ASSERT(push_ready_a, push_ready == expected_push_ready)
  `BR_ASSERT(forward_progress_a, all_valid && pop_ready |-> pop_valid_unstable)
  `BR_ASSERT(no_spurious_pop_a, pop_valid_unstable && pop_ready |-> |(push_valid & push_ready))

  for (genvar i = 0; i < NumFlows; i++) begin : gen_flow_checks
    if (NumFlows > 1 || AllowEmptySelect) begin : gen_unselected
      `BR_ASSERT(unselected_not_ready_a, !select_multihot[i] |-> !push_ready[i])
    end
    `BR_ASSERT(
        transfer_lockstep_a,
        (push_valid[i] && push_ready[i]) == (select_multihot[i] && pop_valid_unstable && pop_ready))
  end

  if (AllowEmptySelect) begin : gen_empty_select
    `BR_ASSERT(empty_select_no_pop_a, select_multihot == '0 |-> !pop_valid_unstable)
    if (!EnableAssertNoPushBackpressure) begin : gen_valid_unselected
      // Exercise empty selection with traffic present; this must not be assumed away.
      `BR_COVER(empty_select_valid_c, select_multihot == '0 && push_valid != '0 && pop_ready)
    end
  end

  // ----------FV covers----------
  `BR_COVER(all_selected_transfer_c,
            (&select_multihot) && (&push_valid) && (&push_ready) && pop_valid_unstable && pop_ready)

  if (EnableCoverPushBackpressure) begin : gen_backpressure_covers
    `BR_COVER(stall_release_c,
              (all_valid && pop_valid_unstable && !pop_ready) ##1
              (all_valid && pop_valid_unstable && pop_ready))
  end

endmodule : br_flow_join_select_multihot_fpv_monitor

bind br_flow_join_select_multihot br_flow_join_select_multihot_fpv_monitor #(
    .NumFlows(NumFlows),
    .AllowEmptySelect(AllowEmptySelect),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
) monitor (.*);
