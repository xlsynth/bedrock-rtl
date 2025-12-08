// SPDX-License-Identifier: Apache-2.0


// Basic checker of br_flow_mux

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_mux_basic_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableCoverPopBackpressure = EnableCoverPushBackpressure,
    parameter bit EnableAssertPopValidStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPopDataStability = 0,
    parameter bit EnableAssertMustGrant = 1,
    parameter bit DelayedGrant = 0
) (
    input logic                           clk,
    input logic                           rst,
    input logic [NumFlows-1:0]            push_ready,
    input logic [NumFlows-1:0]            push_valid,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid,
    input logic [   Width-1:0]            pop_data
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
    if (EnableAssertPushDataStability) begin : gen_push_data
      `BR_ASSUME(push_data_stable_a, push_valid[n] && !push_ready[n] |=> $stable(push_data[n]))
    end
  end

  // ----------Sanity Check----------
  if (EnableAssertPopValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  end
  if (EnableCoverPopBackpressure) begin : gen_pop_backpressure
    if (EnableAssertPopDataStability) begin : gen_pop_data_stable
      `BR_ASSERT(pop_data_stable_a, pop_valid && !pop_ready |=> pop_valid && $stable(pop_data))
    end else begin : gen_pop_data_unstable
      `BR_COVER(pop_data_unstable_c, (pop_valid && !pop_ready) ##1 !$stable(pop_data))
    end
  end

  // ----------Critical Covers----------
  if (EnableCoverPushBackpressure) begin : gen_cover_all_push_valid
    `BR_COVER(all_push_valid_c, &push_valid)
  end

  // ----------Forward Progress Check----------
  if (EnableAssertMustGrant) begin : gen_must_grant
    if (DelayedGrant) begin : gen_delayed_grant
      `BR_ASSERT(must_grant_a, |push_valid |=> pop_valid)
    end else begin : gen_immediate_grant
      `BR_ASSERT(must_grant_a, |push_valid == pop_valid)
    end
  end

endmodule : br_flow_mux_basic_fpv_monitor
