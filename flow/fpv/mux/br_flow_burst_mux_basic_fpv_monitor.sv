// SPDX-License-Identifier: Apache-2.0


// Basic checker of br_flow_burst_mux

`include "br_asserts.svh"
`include "br_fv.svh"
`include "br_registers.svh"

module br_flow_burst_mux_basic_fpv_monitor #(
    parameter int NumFlows = 1,
    parameter int Width = 1,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableCoverPopBackpressure = EnableCoverPushBackpressure,
    parameter bit EnableAssertPopValidStability = EnableAssertPushValidStability,
    parameter bit EnableAssertPopDataStability = 0
) (
    input logic                           clk,
    input logic                           rst,
    input logic [NumFlows-1:0]            push_ready,
    input logic [NumFlows-1:0]            push_valid,
    input logic [NumFlows-1:0]            push_last,
    input logic [NumFlows-1:0][Width-1:0] push_data,
    input logic                           pop_ready,
    input logic                           pop_valid,
    input logic                           pop_last,
    input logic [   Width-1:0]            pop_data
);

  localparam int FlowIdWidth = NumFlows == 1 ? 1 : $clog2(NumFlows);

  logic [FlowIdWidth-1:0] magic_flow;
  logic magic_push_hs;
  logic magic_pop_hs;

  // Width must be large enough to hold the flow index in the low bits for coloring.
  `BR_ASSERT_STATIC(width_gte_flowidwidth_a, Width >= FlowIdWidth)

  // ----------FV assumptions----------
  `BR_ASSUME(pop_ready_liveness_a, s_eventually (pop_ready))
  `BR_ASSUME(magic_flow_stable_a, $stable(magic_flow) && (magic_flow < NumFlows))

  for (genvar n = 0; n < NumFlows; n++) begin : gen_asm
    // Color the low bits of each flow's payload with that flow's index.
    `BR_ASSUME(color_push_data_a, push_valid[n] |-> push_data[n][FlowIdWidth-1:0] == n)
    if (!EnableCoverPushBackpressure) begin : gen_no_backpressure
      `BR_ASSUME(no_backpressure_a, !push_ready[n] |-> !push_valid[n])
    end
    if (EnableAssertPushValidStability) begin : gen_push_valid
      `BR_ASSUME(push_valid_stable_a, push_valid[n] && !push_ready[n] |=> push_valid[n])
    end
    if (EnableAssertPushDataStability) begin : gen_push_data
      `BR_ASSUME(push_data_stable_a,
                 push_valid[n] && !push_ready[n] |=> $stable(push_data[n]) && $stable(push_last[n]))
    end
  end

  // ----------Sanity Check----------
  if (EnableAssertPopValidStability) begin : gen_pop_valid
    `BR_ASSERT(pop_valid_stable_a, pop_valid && !pop_ready |=> pop_valid)
  end
  if (EnableCoverPopBackpressure) begin : gen_pop_backpressure
    if (EnableAssertPopDataStability) begin : gen_pop_data_stable
      `BR_ASSERT(pop_data_stable_a,
                 pop_valid && !pop_ready |=> pop_valid && $stable(pop_data) && $stable(pop_last))
    end else begin : gen_pop_data_unstable
      `BR_COVER(pop_data_unstable_c,
                (pop_valid && !pop_ready) ##1 (!$stable(pop_data) || !$stable(pop_last)))
    end
  end

  // ----------Burst Check----------
  assign magic_push_hs = push_valid[magic_flow] && push_ready[magic_flow];
  assign magic_pop_hs  = pop_valid && pop_ready && (pop_data[FlowIdWidth-1:0] == magic_flow);

  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width + 1),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1)
  ) burst_sb (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(magic_push_hs),
      .incoming_data({push_data[magic_flow], push_last[magic_flow]}),
      .outgoing_vld(magic_pop_hs),
      .outgoing_data({pop_data, pop_last})
  );

  // ----------Critical Covers----------
  if (EnableCoverPushBackpressure) begin : gen_cover_all_push_valid
    `BR_COVER(all_push_valid_c, &push_valid)
  end

  // ----------Forward Progress Check----------
  `BR_ASSERT(must_grant_a, |(push_valid & push_ready) |=> pop_valid)

endmodule : br_flow_burst_mux_basic_fpv_monitor
