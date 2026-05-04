// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for br_credit_sender behavior while the receiver is in reset.

`include "br_asserts.svh"

module br_credit_sender_receiver_reset_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int NumFlows = 2;
  localparam int Width = 8;
  localparam int MaxCredit = 2;
  localparam int PopCreditMaxChange = 1;
  localparam int CounterWidth = $clog2(MaxCredit + 1);
  localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1);

  logic [NumFlows-1:0] push_ready;
  logic [NumFlows-1:0] push_valid;
  logic [NumFlows-1:0][Width-1:0] push_data;
  logic pop_sender_in_reset;
  logic pop_receiver_in_reset;
  logic [PopCreditWidth-1:0] pop_credit;
  logic [NumFlows-1:0] pop_valid;
  logic [NumFlows-1:0][Width-1:0] pop_data;
  logic [CounterWidth-1:0] credit_initial;
  logic [CounterWidth-1:0] credit_withhold;
  logic [CounterWidth-1:0] credit_count;
  logic [CounterWidth-1:0] credit_available;

  br_credit_sender #(
      .NumFlows(NumFlows),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .PopCreditMaxChange(PopCreditMaxChange),
      .RegisterPopOutputs(0)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_valid,
      .pop_data,
      .credit_initial,
      .credit_withhold,
      .credit_count,
      .credit_available
  );

  assign credit_initial = CounterWidth'(MaxCredit);
  assign credit_withhold = '0;
  assign push_valid = !rst ? '1 : '0;
  assign push_data[0] = 8'h40;
  assign push_data[1] = 8'h41;
  assign pop_receiver_in_reset = !rst;
  assign pop_credit = '0;

  `BR_ASSERT(no_push_ready_while_receiver_reset_a,
             !rst && pop_receiver_in_reset |-> push_ready == '0)
  `BR_ASSERT(no_pop_valid_while_receiver_reset_a,
             !rst && pop_receiver_in_reset |-> pop_valid == '0)

endmodule : br_credit_sender_receiver_reset_fpv_repro
