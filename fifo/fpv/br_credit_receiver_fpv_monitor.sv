// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// FIFO br_credit_receiver FPV checks

`include "br_asserts.svh"
`include "br_registers.svh"

module br_credit_receiver_fpv_monitor #(
    parameter int MaxCredit = 1,
    parameter int NumWritePorts = 1,
    localparam int PushCreditWidth = $clog2(NumWritePorts + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
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
    input logic [CreditWidth-1:0] credit_available_push
);

  // ----------FV modeling code----------
  logic fv_rst;
  logic [CreditWidth-1:0] fv_credit_cnt;
  logic [CreditWidth-1:0] fv_max_credit;

  assign fv_rst = rst | push_sender_in_reset;
  `BR_REG(fv_credit_cnt, fv_credit_cnt + $countones(push_credit) - $countones(push_valid))
  `BR_REGIX(fv_max_credit, fv_max_credit, credit_initial_push, clk, fv_rst)

  // ----------FV assumptions----------
  `BR_ASSUME(push_sender_in_reset_a, !push_sender_in_reset |=> !push_sender_in_reset)
  `BR_ASSUME(credit_withhold_push_a, credit_withhold_push <= MaxCredit)
  `BR_ASSUME(credit_withhold_liveness_a, s_eventually (credit_withhold_push < fv_max_credit))
  `BR_ASSUME(no_spurious_push_valid_a, fv_credit_cnt == 'd0 |-> push_valid == 'd0)

  // ----------FV assertions----------
  `BR_ASSERT(fv_credit_sanity_a, fv_credit_cnt <= fv_max_credit)
  `BR_ASSERT(push_credit_deadlock_a, push_valid != 'd0 |-> s_eventually (fv_credit_cnt != 'd0))

endmodule : br_credit_receiver_fpv_monitor
