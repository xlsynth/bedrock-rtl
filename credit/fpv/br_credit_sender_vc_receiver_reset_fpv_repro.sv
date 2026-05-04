// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for br_credit_sender_vc behavior while the receiver is in reset.

`include "br_asserts.svh"

module br_credit_sender_vc_receiver_reset_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int NumVcs = 2;
  localparam int Width = 8;
  localparam int MaxCredit = 1;
  localparam int PopCreditMaxChange = 1;
  localparam int VcWidth = $clog2(NumVcs);
  localparam int CounterWidth = $clog2(MaxCredit + 1);
  localparam int PopCreditWidth = $clog2(PopCreditMaxChange + 1);

  logic [NumVcs-1:0] request;
  logic [NumVcs-1:0] can_grant;
  logic [NumVcs-1:0] grant;
  logic enable_priority_update;
  logic [NumVcs-1:0] push_ready;
  logic [NumVcs-1:0] push_valid;
  logic [NumVcs-1:0][Width-1:0] push_data;
  logic pop_sender_in_reset;
  logic pop_receiver_in_reset;
  logic [NumVcs-1:0][PopCreditWidth-1:0] pop_credit;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic [VcWidth-1:0] pop_vc;
  logic [NumVcs-1:0][CounterWidth-1:0] credit_initial;
  logic [NumVcs-1:0][CounterWidth-1:0] credit_withhold;
  logic [NumVcs-1:0][CounterWidth-1:0] credit_count;
  logic [NumVcs-1:0][CounterWidth-1:0] credit_available;

  br_credit_sender_vc #(
      .NumVcs(NumVcs),
      .Width(Width),
      .MaxCredit(MaxCredit),
      .PopCreditMaxChange(PopCreditMaxChange),
      .RegisterPopOutputs(0)
  ) dut (
      .clk,
      .rst,
      .request,
      .can_grant,
      .grant,
      .enable_priority_update,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset,
      .pop_receiver_in_reset,
      .pop_credit,
      .pop_valid,
      .pop_data,
      .pop_vc,
      .credit_initial,
      .credit_withhold,
      .credit_count,
      .credit_available
  );

  assign can_grant = request[0] ? 2'b01 : request[1] ? 2'b10 : 2'b00;
  assign grant = request & can_grant;
  assign push_valid = !rst ? 2'b01 : '0;
  assign push_data[0] = 8'h51;
  assign push_data[1] = 8'h52;
  assign pop_receiver_in_reset = !rst;
  assign pop_credit = '0;
  assign credit_initial = '1;
  assign credit_withhold = '0;

  `BR_ASSERT(no_push_ready_while_receiver_reset_a,
             !rst && pop_receiver_in_reset |-> push_ready == '0)
  `BR_ASSERT(no_pop_valid_while_receiver_reset_a,
             !rst && pop_receiver_in_reset |-> !pop_valid)

endmodule : br_credit_sender_vc_receiver_reset_fpv_repro
