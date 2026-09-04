// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL pop valid/credit FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_pop_credit_fpv_monitor #(
    parameter int NumPopPorts = 1,
    parameter int MaxCredit = 1,
    parameter int PopCreditMaxChange = 1,
    parameter bit EnableCoverCreditWithhold = 1,
    localparam int CreditWidth = $clog2(MaxCredit + 1),
    localparam int CreditCalcWidth = CreditWidth + 1,
    localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1)
) (
    input logic clk,
    input logic rst,

    // Pop-side reset interface.
    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,

    // Pop-side credit/valid interface.
    input logic [PopCreditWidth-1:0] pop_credit,
    input logic [NumPopPorts-1:0] pop_valid,

    // Pop-side credits.
    input logic [CreditWidth-1:0] credit_initial_pop,
    input logic [CreditWidth-1:0] credit_withhold_pop,
    input logic [CreditWidth-1:0] credit_count_pop,
    input logic [CreditWidth-1:0] credit_available_pop
);
  logic fv_rst;
  logic [CreditWidth-1:0] fv_credit_cnt;
  logic [CreditCalcWidth-1:0] fv_credit_cnt_next;
  logic [CreditWidth-1:0] fv_max_credit;

  assign fv_rst = rst || pop_receiver_in_reset;
  assign fv_credit_cnt_next = fv_credit_cnt + pop_credit - $countones(pop_valid);
  `BR_REGIX(fv_credit_cnt, fv_credit_cnt_next[CreditWidth-1:0], credit_initial_pop, clk, fv_rst)
  `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial_pop, clk, fv_rst)

  // ----------FV assumptions----------
  `BR_ASSUME(credit_initial_pop_a, credit_initial_pop <= MaxCredit)
  `BR_ASSUME(credit_withhold_pop_a, credit_withhold_pop <= credit_initial_pop)
  `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold_pop < fv_max_credit))
  `BR_ASSUME(legal_pop_credit_a, pop_credit <= PopCreditMaxChange)
  `BR_ASSUME(no_spurious_pop_credit_a, fv_max_credit - fv_credit_cnt + $countones(pop_valid)
             >= pop_credit)

  if (EnableCoverCreditWithhold) begin : gen_withhold
    `BR_COVER(credit_withhold_nonzero_a, credit_withhold_pop != '0)
  end else begin : gen_no_withhold
    `BR_ASSUME(credit_withhold_zero_a, credit_withhold_pop == '0)
  end

  // ----------FV assertions----------
  `BR_ASSERT(fv_credit_sanity_a, fv_credit_cnt <= fv_max_credit)
  `BR_ASSERT(no_spurious_pop_valid_a, fv_credit_cnt + pop_credit == '0 |-> pop_valid == '0)

endmodule : br_pop_credit_fpv_monitor
