// SPDX-License-Identifier: Apache-2.0


// FIFO br_credit_receiver FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_credit_receiver_fpv_monitor #(
    parameter bit PStatic = 0,
    parameter int MaxCredit = 1,
    parameter int NumWritePorts = 1,
    parameter bit EnableCoverPushCreditStall = 1,
    parameter bit EnableCoverCreditWithhold = 1,
    parameter bit EnableCoverPushSenderInReset = 1,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1),
    localparam int AddrWidth = br_math::clamped_clog2(MaxCredit)
) (
    input logic clk,
    input logic rst,

    // Push-side interface
    input logic push_sender_in_reset,
    input logic push_receiver_in_reset,
    input logic push_credit_stall,
    input logic [PushCreditWidth-1:0] push_credit,
    input logic [NumWritePorts-1:0] push_valid,

    // Push-side credits
    input logic [CreditWidth-1:0] credit_initial_push,
    input logic [CreditWidth-1:0] credit_withhold_push,
    input logic [CreditWidth-1:0] credit_count_push,
    input logic [CreditWidth-1:0] credit_available_push,

    // psudo-static allocation
    input logic [AddrWidth-1:0] config_base,
    input logic [AddrWidth-1:0] config_bound
);

  // ----------FV modeling code----------
  logic fv_rst;
  logic [CreditWidth-1:0] fv_credit_cnt, fv_credit_cnt_nxt;
  logic [CreditWidth-1:0] fv_max_credit;
  logic [CreditWidth-1:0] config_max;

  assign fv_rst = rst | push_sender_in_reset;
  assign fv_credit_cnt_nxt = fv_credit_cnt + push_credit - $countones(push_valid);
  `BR_REG(fv_credit_cnt, fv_credit_cnt_nxt)
  `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial_push, clk, fv_rst)
  assign config_max = config_bound - config_base + 'd1;

  // ----------FV assumptions----------
  `BR_ASSUME(push_sender_in_reset_a, !push_sender_in_reset |=> !push_sender_in_reset)
  if (PStatic == 1) begin : gen_pstatic
    `BR_ASSUME(credit_withhold_push_a, credit_withhold_push <= config_max)
    `BR_ASSUME(credit_initial_push_a, credit_initial_push <= config_max)
  end else begin : gen_static
    `BR_ASSUME(credit_withhold_push_a, credit_withhold_push <= MaxCredit)
  end
  `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold_push < fv_max_credit))
  `BR_ASSUME(push_credit_stall_liveness_a, s_eventually !push_credit_stall)
  `BR_ASSUME(no_credit_cnt_overflow_a, push_credit > $countones(push_valid)
                                       |-> fv_credit_cnt_nxt > fv_credit_cnt)
  `BR_ASSUME(no_credit_cnt_underflow_a, push_credit < $countones(push_valid)
                                        |-> fv_credit_cnt_nxt < fv_credit_cnt)
  `BR_ASSUME(no_spurious_push_valid_a, fv_credit_cnt == 'd0 |-> push_valid == 'd0)
  if (EnableCoverPushCreditStall) begin : gen_stall
    `BR_COVER(push_credit_stall_a, push_credit_stall)
  end else begin : gen_no_stall
    `BR_ASSUME(no_push_credit_stall_a, !push_credit_stall)
  end
  if (EnableCoverCreditWithhold) begin : gen_withhold
    `BR_COVER(credit_withhold_nonzero_a, credit_withhold_push != 'd0)
  end else begin : gen_no_withhold
    `BR_ASSUME(credit_withhold_zero_a, credit_withhold_push == 'd0)
  end
  if (EnableCoverPushSenderInReset) begin : gen_reset
    `BR_COVER(push_sender_in_reset_a, push_sender_in_reset)
  end else begin : gen_no_reset
    `BR_ASSUME(no_push_sender_in_reset_a, !push_sender_in_reset)
  end

  // ----------FV assertions----------
  `BR_ASSERT(fv_credit_sanity_a, fv_credit_cnt <= fv_max_credit)
  `BR_ASSERT(push_credit_deadlock_a, $countones(push_valid)
                                     != push_credit |-> s_eventually (fv_credit_cnt != 'd0))

endmodule : br_credit_receiver_fpv_monitor
