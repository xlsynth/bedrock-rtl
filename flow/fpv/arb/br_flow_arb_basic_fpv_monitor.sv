// SPDX-License-Identifier: Apache-2.0

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_arb_basic_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure
) (
    input logic                clk,
    input logic                rst,
    input logic [NumFlows-1:0] push_ready,
    input logic [NumFlows-1:0] push_valid,
    input logic                pop_ready,
    input logic                pop_valid_unstable
);

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))

  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    if (!EnableCoverPushBackpressure) begin : gen_no_backpressure
      `BR_ASSUME(no_backpressure_a, !push_ready[n] |-> !push_valid[n])
    end
    if (EnableAssertPushValidStability) begin : gen_push_valid
      `BR_ASSUME(push_valid_stable_a, push_valid[n] && !push_ready[n] |=> push_valid[n])
    end
  end

  // ----------Sanity Check----------
  if (EnableAssertPushValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid_unstable && !pop_ready |=> pop_valid_unstable)
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |push_valid == pop_valid_unstable)

  // ----------Critical Covers----------
  if (EnableCoverPushBackpressure) begin : gen_cover_all_push_valid
    `BR_COVER(all_push_valid_c, &push_valid)
  end

endmodule : br_flow_arb_basic_fpv_monitor
