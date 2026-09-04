// SPDX-License-Identifier: Apache-2.0

// Pop-credit model for FIFOs where credit is consumed on an issue before the
// corresponding pop_valid response returns. pop_issue marks an accepted read
// request for one FIFO: it spends one receiver-owned credit when the request
// launches, while pop_valid later returns that credit after the RAM response
// latency. The generic pop-credit checker assumes issue and response coincide,
// so keep this model local to this DUT.
`include "br_asserts.svh"
`include "br_registers.svh"

module br_fifo_shared_dynamic_pop_credit_fpv_checker #(
    parameter int NumPopPorts = 1,
    parameter int MaxCredit = 1,
    parameter int PopCreditMaxChange = 1,
    localparam int CreditWidth = $clog2(MaxCredit + 1),
    localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1),
    localparam int ModelWidth = $clog2(MaxCredit + NumPopPorts + PopCreditMaxChange + 1) + 1
) (
    input logic clk,
    input logic rst,
    input logic pop_sender_in_reset,
    input logic pop_receiver_in_reset,
    input logic [PopCreditWidth-1:0] pop_credit,
    input logic [NumPopPorts-1:0] pop_valid,
    input logic [NumPopPorts-1:0] pop_issue,
    input logic [CreditWidth-1:0] credit_initial_pop,
    input logic [CreditWidth-1:0] credit_withhold_pop,
    input logic [CreditWidth-1:0] credit_count_pop,
    input logic [CreditWidth-1:0] credit_available_pop
);
  logic link_rst;
  logic receiver_active_rst;
  logic [ModelWidth-1:0] modeled_credit_count, modeled_credit_count_next;
  logic [ModelWidth-1:0] modeled_credit_available;
  logic [ModelWidth-1:0] receiver_owned_credit, receiver_owned_credit_next;
  logic [ModelWidth-1:0] count_plus_credit;
  logic [ModelWidth-1:0] effective_pop_credit;
  logic receiver_credit_in_range;
  localparam logic [ModelWidth-1:0] ModelMaxCredit = MaxCredit;

  assign link_rst = rst || pop_sender_in_reset || pop_receiver_in_reset;
  assign receiver_active_rst = rst || pop_receiver_in_reset;
  // A reset-time pop_credit is link handshaking, not a normal credit return.
  // Keep the registered reset state for assertion sampling and ignore that
  // handshaking while the receiver side is reset.
  assign effective_pop_credit = receiver_active_rst ? '0 : ModelWidth'(pop_credit);
  assign count_plus_credit = modeled_credit_count + effective_pop_credit;
  assign modeled_credit_count_next = count_plus_credit - ModelWidth'($countones(pop_issue));
  assign modeled_credit_available = receiver_active_rst ?
      (receiver_owned_credit > ModelWidth'(credit_withhold_pop) ?
       receiver_owned_credit - ModelWidth'(credit_withhold_pop) : '0) :
      count_plus_credit > ModelWidth'(credit_withhold_pop) ?
      count_plus_credit - ModelWidth'(credit_withhold_pop) : '0;
  assign receiver_owned_credit_next = receiver_owned_credit + ModelWidth'($countones(
      pop_valid
  )) - effective_pop_credit;
  assign receiver_credit_in_range = receiver_owned_credit <= ModelMaxCredit &&
      receiver_owned_credit_next <= ModelMaxCredit;
  `BR_REGIX(modeled_credit_count, modeled_credit_count_next, ModelWidth'(credit_initial_pop), clk,
            link_rst)
  `BR_REGIX(receiver_owned_credit, receiver_owned_credit_next,
            ModelMaxCredit - ModelWidth'(credit_initial_pop), clk, link_rst)

  `BR_ASSUME(credit_initial_pop_a, credit_initial_pop <= MaxCredit)
  `BR_ASSUME(credit_initial_pop_stable_a, $stable(credit_initial_pop))
  `BR_ASSUME(credit_withhold_pop_a, credit_withhold_pop <= MaxCredit)
  `BR_ASSUME(legal_pop_credit_a, pop_credit <= PopCreditMaxChange)
  `BR_ASSUME_CR(pop_returns_owned_credit_a,
                ModelWidth'(pop_credit) <= receiver_owned_credit + ModelWidth'($countones
                (pop_valid)), clk, receiver_active_rst)

  `BR_ASSERT(pop_credit_count_a, ModelWidth'(credit_count_pop) == modeled_credit_count)
  `BR_ASSERT(pop_credit_available_a, ModelWidth'(credit_available_pop) == modeled_credit_available)
  `BR_ASSERT(pop_credit_capacity_a,
             modeled_credit_count <= ModelMaxCredit && modeled_credit_count_next <= ModelMaxCredit)
  `BR_ASSERT(receiver_credit_capacity_a, receiver_credit_in_range)
  `BR_ASSERT(issue_has_credit_a, ModelWidth'($countones(pop_issue)) <= modeled_credit_available)
  `BR_ASSERT(credit_ownership_conservation_a,
             modeled_credit_count_next + receiver_owned_credit_next <= ModelMaxCredit)
endmodule : br_fifo_shared_dynamic_pop_credit_fpv_checker
