// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL pop valid/credit FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_pop_credit_fpv_monitor #(
    parameter int NumPopPorts = 1,
    parameter int MaxCredit = 1,
    parameter int PopCreditMaxChange = 1,
    parameter bit EnableCoverCreditWithhold = 1,
    parameter bit UseExplicitCreditOwnership = 0,
    parameter bit EnableLiveness = 1,
    localparam int CreditWidth = $clog2(MaxCredit + 1),
    localparam int CreditCalcWidth = CreditWidth + 1,
    localparam int CreditModelWidth = $clog2(MaxCredit + NumPopPorts + PopCreditMaxChange + 1) + 1,
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
    // Credit-consuming issues, which can precede the actual pop_valid responses.
    // Ignored when UseExplicitCreditOwnership is zero.
    input logic [NumPopPorts-1:0] pop_issue,

    // Pop-side credits.
    input logic [CreditWidth-1:0] credit_initial_pop,
    input logic [CreditWidth-1:0] credit_withhold_pop,
    input logic [CreditWidth-1:0] credit_count_pop,
    input logic [CreditWidth-1:0] credit_available_pop,

    output logic [CreditModelWidth-1:0] modeled_credit_count,
    output logic [CreditModelWidth-1:0] modeled_credit_count_next,
    output logic [CreditModelWidth-1:0] modeled_credit_available,
    output logic [CreditModelWidth-1:0] receiver_owned_credit,
    output logic [CreditModelWidth-1:0] receiver_owned_credit_next
);
  if (UseExplicitCreditOwnership) begin : gen_explicit_ownership
    logic link_rst;
    logic receiver_active_rst;
    logic [CreditModelWidth-1:0] count_plus_credit;

    // The reset boundary is the pop link, independent of other FIFO interfaces.
    assign link_rst = rst || pop_sender_in_reset || pop_receiver_in_reset;
    assign receiver_active_rst = rst || pop_receiver_in_reset;
    assign count_plus_credit = modeled_credit_count + CreditModelWidth'(pop_credit);
    assign modeled_credit_count_next = count_plus_credit - CreditModelWidth'($countones(pop_issue));
    assign modeled_credit_available = count_plus_credit > CreditModelWidth'(credit_withhold_pop) ?
        count_plus_credit - CreditModelWidth'(credit_withhold_pop) : '0;
    assign receiver_owned_credit_next = receiver_owned_credit + CreditModelWidth'($countones(
        pop_valid
    )) - CreditModelWidth'(pop_credit);
    `BR_REGIX(modeled_credit_count, modeled_credit_count_next,
              CreditModelWidth'(credit_initial_pop), clk, link_rst)
    `BR_REGIX(receiver_owned_credit, receiver_owned_credit_next,
              CreditModelWidth'(MaxCredit) - CreditModelWidth'(credit_initial_pop), clk, link_rst)

    // Configuration remains constrained during either endpoint's reset.
    `BR_ASSUME_CR(credit_initial_pop_a, credit_initial_pop <= MaxCredit, clk, rst)
    `BR_ASSUME_CR(credit_initial_pop_stable_a, $stable(credit_initial_pop), clk, rst)
    `BR_ASSUME_CR(credit_withhold_pop_a, credit_withhold_pop <= MaxCredit, clk, rst)
    `BR_ASSUME_CR(legal_pop_credit_a, pop_credit <= PopCreditMaxChange, clk, rst)
    // Only delivered responses replenish the receiver. An issue alone cannot
    // authorize a returned credit while that response is still in flight.
    // Return legality remains checked whenever the receiver is out of reset.
    `BR_ASSUME_CR(
        pop_returns_owned_credit_a,
        CreditModelWidth'(pop_credit) <= receiver_owned_credit + CreditModelWidth'($countones(
        pop_valid)), clk, receiver_active_rst)

    `BR_ASSERT_CR(pop_credit_count_a, CreditModelWidth'(credit_count_pop) == modeled_credit_count,
                  clk, link_rst)
    `BR_ASSERT_CR(pop_credit_available_a,
                  CreditModelWidth'(credit_available_pop) == modeled_credit_available, clk,
                  link_rst)
    `BR_ASSERT_CR(pop_credit_capacity_a,
                  modeled_credit_count <= CreditModelWidth'(MaxCredit) &&
                      modeled_credit_count_next <= CreditModelWidth'(MaxCredit),
                  clk, link_rst)
    `BR_ASSERT_CR(receiver_credit_capacity_a,
                  receiver_owned_credit <= CreditModelWidth'(MaxCredit) &&
                      receiver_owned_credit_next <= CreditModelWidth'(MaxCredit),
                  clk, link_rst)
    `BR_ASSERT_CR(issue_has_credit_a, CreditModelWidth'($countones(pop_issue
                  )) <= modeled_credit_available, clk, link_rst)
    `BR_ASSERT_CR(
        credit_ownership_conservation_a,
        modeled_credit_count_next + receiver_owned_credit_next <= CreditModelWidth'(MaxCredit), clk,
        link_rst)

    if (EnableLiveness) begin : gen_liveness
      `BR_ASSUME_CR(credit_withhold_liveness_a, s_eventually (credit_withhold_pop < MaxCredit), clk,
                    link_rst)
    end
    if (!EnableCoverCreditWithhold) begin : gen_no_withhold
      `BR_ASSUME_CR(credit_withhold_zero_a, credit_withhold_pop == '0, clk, link_rst)
    end
  end else begin : gen_legacy
    logic fv_rst;
    logic [CreditWidth-1:0] fv_credit_cnt;
    logic [CreditCalcWidth-1:0] fv_credit_cnt_next;
    logic [CreditWidth-1:0] fv_max_credit;

    assign fv_rst = rst || pop_receiver_in_reset;
    assign fv_credit_cnt_next = fv_credit_cnt + pop_credit - $countones(pop_valid);
    `BR_REGIX(fv_credit_cnt, fv_credit_cnt_next[CreditWidth-1:0], credit_initial_pop, clk, fv_rst)
    `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial_pop, clk, fv_rst)
    assign modeled_credit_count = CreditModelWidth'(fv_credit_cnt);
    assign modeled_credit_count_next = CreditModelWidth'(fv_credit_cnt_next);
    // The legacy contract has no separate issue/response ownership model.
    assign modeled_credit_available = '0;
    assign receiver_owned_credit = '0;
    assign receiver_owned_credit_next = '0;

    `BR_ASSUME(credit_initial_pop_a, credit_initial_pop <= MaxCredit)
    `BR_ASSUME(credit_withhold_pop_a, credit_withhold_pop <= credit_initial_pop)
    if (EnableLiveness) begin : gen_liveness
      `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold_pop < fv_max_credit))
    end
    `BR_ASSUME(legal_pop_credit_a, pop_credit <= PopCreditMaxChange)
    `BR_ASSUME(no_spurious_pop_credit_a, fv_max_credit - fv_credit_cnt + $countones(pop_valid
               ) >= pop_credit)

    if (EnableCoverCreditWithhold) begin : gen_withhold
      `BR_COVER(credit_withhold_nonzero_a, credit_withhold_pop != '0)
    end else begin : gen_no_withhold
      `BR_ASSUME(credit_withhold_zero_a, credit_withhold_pop == '0)
    end

    `BR_ASSERT(fv_credit_sanity_a, fv_credit_cnt <= fv_max_credit)
    `BR_ASSERT(no_spurious_pop_valid_a, fv_credit_cnt + pop_credit == '0 |-> pop_valid == '0)
  end

endmodule : br_pop_credit_fpv_monitor
