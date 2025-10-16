// SPDX-License-Identifier: Apache-2.0


// Basic checker of br_flow_demux

`include "br_asserts.svh"
`include "br_fv.svh"

module br_flow_demux_basic_fpv_monitor #(
    parameter int NumFlows = 2,  // Must be at least 2
    parameter int Width = 1,  // Must be at least 1
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertSelectStability = 0,
    parameter bit EnableAssertPopValidStability = 1,
    parameter bit EnableAssertPopDataStability = 1
) (
    input logic                                   clk,
    input logic                                   rst,
    input logic [$clog2(NumFlows)-1:0]            select,
    input logic                                   push_ready,
    input logic                                   push_valid,
    input logic [           Width-1:0]            push_data,
    input logic [        NumFlows-1:0]            pop_ready,
    input logic [        NumFlows-1:0]            pop_valid,
    input logic [        NumFlows-1:0][Width-1:0] pop_data
);

  // pick a random constant for assertion
  logic [$clog2(NumFlows)-1:0] fv_idx;
  `BR_ASSUME(fv_idx_a, $stable(fv_idx) && fv_idx < NumFlows)

  // ----------FV assumptions----------
  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready[n]))
  end

  if (EnableAssertPushValidStability) begin : gen_push_valid
    `BR_ASSUME(push_valid_stable_a, push_valid && !push_ready |=> push_valid)
  end
  if (EnableAssertPushDataStability) begin : gen_push_data
    `BR_ASSUME(push_data_stable_a, push_valid && !push_ready |=> $stable(push_data))
  end

  if (!EnableCoverPushBackpressure) begin : gen_no_push_backpressure
    `BR_ASSUME(no_push_backpressure_a, !push_ready |-> !push_valid)
  end

  if (EnableAssertSelectStability) begin : gen_select_stability
    `BR_ASSUME(select_stable_a, push_valid && !push_ready |=> $stable(select))
  end

  // ----------Sanity Check----------
  if (EnableAssertPopValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid[fv_idx] && !pop_ready[fv_idx] |=> pop_valid[fv_idx])
  end
  if (EnableAssertPopDataStability) begin : gen_pop_data
    `BR_ASSERT(pop_data_stable_a,
               pop_valid[fv_idx] && !pop_ready[fv_idx] |=> $stable(pop_data[fv_idx]))
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, push_valid |-> pop_valid[select])

endmodule : br_flow_demux_basic_fpv_monitor
