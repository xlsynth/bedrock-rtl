// SPDX-License-Identifier: Apache-2.0


// Basic checker of br_flow_demux

`include "br_asserts.svh"

module br_flow_fork_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertFinalNotValid = 1
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic push_ready,
    input logic push_valid,

    // Pop-side interfaces
    // pop_valid signals are unstable because they must fall if another pop_ready falls.
    // There is no dependency between pop_valid[i] and pop_ready[i].
    input logic [NumFlows-1:0] pop_ready,
    input logic [NumFlows-1:0] pop_valid_unstable
);

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready[n]))
  end

  if (!EnableCoverPushBackpressure) begin : gen_no_backpressure
    `BR_ASSUME(no_backpressure_a, !push_ready |-> !push_valid)
  end

  // ----------FV assertions----------
  // pick a random constant for assertion
  logic [$clog2(NumFlows)-1:0] fv_idx;
  `BR_ASSUME(fv_idx_a, $stable(fv_idx) && fv_idx < NumFlows)

  `BR_ASSERT(forward_progress_a, push_valid & push_ready |-> pop_valid_unstable[fv_idx])

endmodule : br_flow_fork_fpv_monitor

bind br_flow_fork br_flow_fork_fpv_monitor #(
    .NumFlows(NumFlows),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
