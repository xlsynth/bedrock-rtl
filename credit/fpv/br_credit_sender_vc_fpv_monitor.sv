// SPDX-License-Identifier: Apache-2.0


// br_credit_sender_vc FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_credit_sender_vc_fpv_monitor #(
    parameter int NumVcs = 2,
    parameter int Width = 1,
    parameter int MaxCredit = 1,
    parameter int PopCreditMaxChange = 1,
    parameter bit RegisterPopOutputs = 0,
    parameter bit EnableCoverPushBackpressure = 1,
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    parameter bit EnableAssertFinalNotValid = 1,
    // If 1, assert that push-side backpressure is impossible.
    // Can only be enabled if EnableCoverPushBackpressure is disabled.
    parameter bit EnableAssertNoPushBackpressure = !EnableCoverPushBackpressure,
    localparam int VcWidth = $clog2(NumVcs),
    localparam int CounterWidth = $clog2(MaxCredit + 1),
    localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1)
) (
    input logic clk,
    input logic rst,

    // Interface to external arbiter
    input logic [NumVcs-1:0] request,
    input logic [NumVcs-1:0] can_grant,
    input logic [NumVcs-1:0] grant,
    input logic              enable_priority_update,

    // Ready/valid push interface per VC.
    input logic [NumVcs-1:0]            push_ready,
    input logic [NumVcs-1:0]            push_valid,
    input logic [NumVcs-1:0][Width-1:0] push_data,

    // Credit/valid pop interface.
    input logic                                   pop_sender_in_reset,
    input logic                                   pop_receiver_in_reset,
    input logic [ NumVcs-1:0][PopCreditWidth-1:0] pop_credit,
    input logic                                   pop_valid,
    input logic [  Width-1:0]                     pop_data,
    input logic [VcWidth-1:0]                     pop_vc,

    // Reset value for the credit counters
    input logic [NumVcs-1:0][CounterWidth-1:0] credit_initial,
    // Dynamically withhold credits from circulation
    input logic [NumVcs-1:0][CounterWidth-1:0] credit_withhold,
    // Credit counter state before increment/decrement/withhold.
    input logic [NumVcs-1:0][CounterWidth-1:0] credit_count,
    // Dynamic amount of available credit.
    input logic [NumVcs-1:0][CounterWidth-1:0] credit_available
);
  // ----------FV modeling code----------
  logic [VcWidth-1:0] fv_vc;
  `BR_ASSUME(fv_vc_legal_a, $stable(fv_vc) && fv_vc < NumVcs)

  logic fv_rst;
  logic fv_pop_valid;
  logic [NumVcs-1:0][CounterWidth-1:0] fv_pop_credit_cnt;
  logic [NumVcs-1:0][CounterWidth-1:0] fv_max_credit;

  assign fv_rst = rst | pop_receiver_in_reset;
  assign fv_pop_valid = pop_valid && (pop_vc == fv_vc);

  logic [NumVcs-1:0] fv_pop_grant;
  if (RegisterPopOutputs) begin : gen_registered_pop_grant
    `BR_REGIX(fv_pop_grant, grant, '0, clk, rst)
  end else begin : gen_unregistered_pop_grant
    assign fv_pop_grant = grant;
  end

  for (genvar n = 0; n < NumVcs; n++) begin : gen_fv_credit_model
    logic fv_pop_valid_n;
    assign fv_pop_valid_n = pop_valid && (pop_vc == n);

    `BR_REGIX(fv_pop_credit_cnt[n], fv_pop_credit_cnt[n] + pop_credit[n] - fv_pop_valid_n,
              credit_initial[n], clk, fv_rst)
    `BR_REGIX(fv_max_credit[n], fv_max_credit[n], credit_initial[n], clk, fv_rst)
  end

  // ----------FV assumptions----------
  `BR_ASSUME(pop_receiver_in_reset_a, !pop_receiver_in_reset |=> !pop_receiver_in_reset)

  `BR_ASSUME(arb_onehot_grant_a, $onehot0(grant))
  `BR_ASSUME(arb_legal_grant_a, grant == (request & can_grant))
  `BR_ASSUME(same_cyc_arb_grant_a, |request |-> |grant)
  for (genvar n = 0; n < NumVcs; n++) begin : gen_asm
    logic fv_pop_valid_n;
    assign fv_pop_valid_n = pop_valid && (pop_vc == n);

    `BR_ASSUME(arb_grant_eventually_a, request[n] |-> s_eventually grant[n])
    `BR_ASSUME(credit_withhold_a, credit_withhold[n] <= MaxCredit)
    `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold[n] < fv_max_credit[n]))
    `BR_ASSUME(legal_pop_credit_a, pop_credit[n] <= PopCreditMaxChange)
    `BR_ASSUME(pop_credit_liveness_a,
               fv_pop_credit_cnt[n] < fv_max_credit[n] |-> s_eventually |pop_credit[n])
    `BR_ASSUME(no_spurious_pop_credit_a,
               (fv_max_credit[n] - fv_pop_credit_cnt[n] + fv_pop_valid_n) >= pop_credit[n])

    if (!EnableCoverPushBackpressure &&
        EnableAssertNoPushBackpressure) begin : gen_no_push_backpressure
      `BR_ASSUME(no_push_backpressure_a, !push_ready[n] |-> !push_valid[n])
    end
    if (EnableAssertPushValidStability) begin : gen_push_valid_stable
      `BR_ASSUME(push_valid_stable_a, push_valid[n] && !push_ready[n] |=> push_valid[n])
    end
    if (EnableAssertPushDataStability) begin : gen_push_data_stable
      `BR_ASSUME(push_data_stable_a, push_valid[n] && !push_ready[n] |=> $stable(push_data[n]))
    end
  end

  // ----------FV assertions----------
  // Without push-valid stability, a backpressured push_valid pulse can legally drop before
  // the DUT accepts it, so only an accepted push can require eventual pop.
  if (EnableAssertPushValidStability) begin : gen_push_valid_deadlock_stable
    `BR_ASSERT(push_valid_deadlock_a, push_valid[fv_vc] |-> s_eventually fv_pop_valid)
  end else begin : gen_push_valid_deadlock_unstable
    `BR_ASSERT(push_valid_deadlock_a,
               push_valid[fv_vc] && push_ready[fv_vc] |-> s_eventually fv_pop_valid)
  end
  `BR_ASSERT(no_spurious_pop_valid_a,
             (fv_pop_credit_cnt[fv_vc] + pop_credit[fv_vc]) == 'd0 |-> !fv_pop_valid)

  `BR_ASSERT(pop_vc_legal_a, pop_valid |-> pop_vc < NumVcs)
  `BR_ASSERT(pop_valid_implies_grant_a, pop_valid |-> |fv_pop_grant)
  `BR_ASSERT(pop_vc_matches_grant_a, pop_valid |-> fv_pop_grant[pop_vc])
  `BR_ASSERT(priority_update_a, enable_priority_update)

  // ----------Data integrity check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxCredit)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid[fv_vc] & push_ready[fv_vc]),
      .incoming_data(push_data[fv_vc]),
      .outgoing_vld(fv_pop_valid),
      .outgoing_data(pop_data)
  );

endmodule : br_credit_sender_vc_fpv_monitor

bind br_credit_sender_vc br_credit_sender_vc_fpv_monitor #(
    .NumVcs(NumVcs),
    .Width(Width),
    .MaxCredit(MaxCredit),
    .PopCreditMaxChange(PopCreditMaxChange),
    .RegisterPopOutputs(RegisterPopOutputs),
    .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
    .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure),
    .EnableAssertPushValidStability(EnableAssertPushValidStability),
    .EnableAssertPushDataStability(EnableAssertPushDataStability),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
