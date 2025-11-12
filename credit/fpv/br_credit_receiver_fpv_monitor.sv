// SPDX-License-Identifier: Apache-2.0


// br_credit_receiver FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_credit_receiver_fpv_monitor #(
    // Number of data flows associated with this receiver. Must be at least 1.
    parameter int NumFlows = 1,
    // Width of the datapath in bits. Must be at least 1.
    parameter int Width = 1,
    // Maximum number of credits that can be stored (inclusive). Must be at least NumFlows.
    parameter int MaxCredit = 1,
    // If 1, add 1 cycle of retiming to push outputs.
    parameter bit RegisterPushOutputs = 0,
    // Maximum number of push credit that can be returned in a single cycle.
    // Must be at least 1 but cannot be greater than MaxCredit.
    parameter int PushCreditMaxChange = 1,
    // Maximum pop credits that can be returned in a single cycle.
    // Must be at least 1 but cannot be greater than MaxCredit.
    parameter int PopCreditMaxChange = 1,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int CounterWidth = $clog2(MaxCredit + 1),
    localparam int PushCreditWidth = $clog2(PushCreditMaxChange + 1),
    localparam int PopCreditChangeWidth = $clog2(PopCreditMaxChange + 1)
) (
    input logic clk,
    input logic rst,

    // Credit/valid push interface.
    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
    input logic push_credit_stall,
    input logic [PushCreditWidth-1:0] push_credit,
    input logic [NumFlows-1:0] push_valid,
    input logic [NumFlows-1:0][Width-1:0] push_data,

    // Credit/valid pop interface.
    input logic [PopCreditChangeWidth-1:0]            pop_credit,
    input logic [            NumFlows-1:0]            pop_valid,
    input logic [            NumFlows-1:0][Width-1:0] pop_data,

    // Reset value for the credit counter
    input logic [CounterWidth-1:0] credit_initial,
    // Dynamically withhold credits from circulation
    input logic [CounterWidth-1:0] credit_withhold,
    // Credit counter state before increment/decrement/withhold.
    input logic [CounterWidth-1:0] credit_count,
    // Dynamic amount of available credit.
    input logic [CounterWidth-1:0] credit_available
);

  // ----------FV modeling code----------
  localparam int N = NumFlows == 1 ? 1 : $clog2(NumFlows);
  logic [N-1:0] fv_flow;
  `BR_ASSUME(fv_flow_legal_a, $stable(fv_flow) && fv_flow < NumFlows)

  logic fv_rst;
  logic [CounterWidth-1:0] fv_push_credit_cnt;
  logic [CounterWidth-1:0] fv_pop_credit_cnt;
  logic [CounterWidth-1:0] fv_max_credit;

  assign fv_rst = rst | push_sender_in_reset;
  `BR_REG(fv_push_credit_cnt, fv_push_credit_cnt + push_credit - $countones(push_valid))
  `BR_REGIX(fv_pop_credit_cnt, fv_pop_credit_cnt + pop_credit - $countones(pop_valid),
            credit_initial, clk, fv_rst)
  `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial, clk, fv_rst)

  // ----------FV assumptions----------
  `BR_ASSUME(push_sender_in_reset_a, !push_sender_in_reset |=> !push_sender_in_reset)
  `BR_ASSUME(credit_withhold_a, credit_withhold <= MaxCredit)
  `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold < fv_max_credit))
  `BR_ASSUME(no_spurious_push_valid_a, fv_push_credit_cnt + push_credit >= $countones(push_valid))
  `BR_ASSUME(no_spurious_pop_credit_a, (fv_max_credit - fv_pop_credit_cnt + $countones(pop_valid)
             ) >= pop_credit)
  `BR_ASSUME(legal_pop_credit_a, pop_credit <= PopCreditMaxChange)

  // ----------FV assertions----------
  `BR_ASSERT(legal_push_credit_a, push_credit <= PushCreditMaxChange)
  `BR_ASSERT(fv_credit_sanity_a, fv_push_credit_cnt <= fv_max_credit)
  `BR_ASSERT(push_credit_deadlock_a,
             |push_valid && (push_credit == 'd0) |-> s_eventually (fv_push_credit_cnt != 'd0))
  `BR_ASSERT(no_spurious_pop_valid_a, (fv_pop_credit_cnt + pop_credit) == 'd0 |-> pop_valid == 'd0)
  // ----------Data integrity Check----------
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(Width),
      .IN_CHUNKS(1),
      .OUT_CHUNKS(1),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(MaxCredit)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(push_valid[fv_flow]),
      .incoming_data(push_data[fv_flow]),
      .outgoing_vld(pop_valid[fv_flow]),
      .outgoing_data(pop_data[fv_flow])
  );

endmodule : br_credit_receiver_fpv_monitor

bind br_credit_receiver br_credit_receiver_fpv_monitor #(
    .NumFlows(NumFlows),
    .Width(Width),
    .MaxCredit(MaxCredit),
    .RegisterPushOutputs(RegisterPushOutputs),
    .PushCreditMaxChange(PushCreditMaxChange),
    .PopCreditMaxChange(PopCreditMaxChange),
    .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
) monitor (.*);
