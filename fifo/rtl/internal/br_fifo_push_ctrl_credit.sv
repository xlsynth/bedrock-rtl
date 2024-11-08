// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL FIFO Push Controller (Credit/Valid)

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_push_ctrl_credit #(
    parameter int Depth = 2,
    parameter int BitWidth = 1,
    parameter bit EnableBypass = 0,
    parameter int MaxCredit = Depth,
    parameter bit RegisterPushCredit = 0,
    localparam int AddrWidth = $clog2(Depth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    input  logic                push_credit_stall,
    output logic                push_credit,
    input  logic                push_valid,
    input  logic [BitWidth-1:0] push_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Push-side credits
    input  logic [CreditWidth-1:0] credit_initial_push,
    input  logic [CreditWidth-1:0] credit_withhold_push,
    output logic [CreditWidth-1:0] credit_count_push,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waiver.
    input logic bypass_ready,  // ri lint_check_waive INEFFECTIVE_NET
    output logic bypass_valid_unstable,
    output logic [BitWidth-1:0] bypass_data_unstable,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [ BitWidth-1:0] ram_wr_data,

    // Internal handshakes between push and pop controllers
    output logic ram_push,
    input  logic ram_pop
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, BitWidth >= 1)
  `BR_ASSERT_STATIC(credit_width_a, CreditWidth >= $clog2(Depth + 1))

  `BR_COVER_INTG(full_c, full)

  // Internal integration checks

  // This is not the tightest possible check, because we are planning to
  // support pipelined RAM access and CDC use cases that require supporting
  // delays between the push controller and pop controller.
  // The tightest possible check is items == 0 |-> !ram_pop.
  // This one is looser because slots == Depth |-> items == 0 (but the
  // converse is not true).
  `BR_ASSERT_IMPL(no_ram_pop_when_all_slots_a, slots == Depth |-> !ram_pop)
  `BR_ASSERT_IMPL(bypass_ready_only_when_not_full_a, bypass_ready |-> !full)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  logic internal_valid;
  logic [BitWidth-1:0] internal_data;

  br_credit_receiver #(
      .BitWidth          (BitWidth),
      .MaxCredit         (MaxCredit),
      .RegisterPushCredit(RegisterPushCredit)
  ) br_credit_receiver (
      .clk,
      .rst,
      .push_credit_stall(push_credit_stall),
      .push_credit(push_credit),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_credit(ram_pop),
      .pop_valid(internal_valid),
      .pop_data(internal_data),
      .credit_initial(credit_initial_push),
      .credit_withhold(credit_withhold_push),
      .credit_count(credit_count_push)
  );

  // RAM path
  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_wr_addr (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(AddrWidth'(1'b0)),
      .incr_valid(ram_wr_valid),
      .incr(1'b1),
      .value(ram_wr_addr),
      .value_next()  // unused
  );

  // Datapath
  assign ram_wr_valid = ram_push;
  if (EnableBypass) begin : gen_bypass
    assign bypass_valid_unstable = internal_valid;
    assign bypass_data_unstable = internal_data;

    assign ram_push = internal_valid && !bypass_ready;
    assign ram_wr_data = internal_data;
  end else begin : gen_no_bypass
    `BR_UNUSED(bypass_ready)
    assign bypass_valid_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
    assign bypass_data_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT

    assign ram_push = internal_valid;
    assign ram_wr_data = internal_data;
  end

  // Status flags
  assign slots_next = ram_push && !ram_pop ? slots - 1 : !ram_push && ram_pop ? slots + 1 : slots;
  assign full_next  = slots_next == 0;

  `BR_REGIL(slots, slots_next, ram_push || ram_pop, Depth)
  `BR_REGL(full, full_next, ram_push || ram_pop)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(ram_wr_addr_in_range_a, ram_wr_valid |-> ram_wr_addr < Depth)

  // Flow control and latency
  `BR_ASSERT_IMPL(push_backpressure_when_full_a, full |-> !push_credit)
  `BR_ASSERT_IMPL(backpressure_latency_1_cycle_a,
                  full && ram_pop |=> !full && (push_credit || push_credit_stall))
  `BR_ASSERT_IMPL(ram_push_and_bypass_mutually_exclusive_a,
                  !(ram_push && bypass_ready && bypass_valid_unstable))
  `BR_COVER_IMPL(bypass_unstable_c, !bypass_ready && bypass_valid_unstable)

  // RAM
  `BR_ASSERT_IMPL(ram_write_a, ram_push |-> ram_wr_valid && ram_wr_data == push_data)

  // Flags
  `BR_ASSERT_IMPL(slots_in_range_a, slots <= Depth)
  `BR_ASSERT_IMPL(slots_next_a, ##1 slots == $past(slots_next))
  `BR_ASSERT_IMPL(push_and_pop_slots_a, ram_push && ram_pop |-> slots_next == slots)
  `BR_ASSERT_IMPL(push_slots_a, ram_push && !ram_pop |-> slots_next == slots - 1)
  `BR_ASSERT_IMPL(pop_slots_a, !ram_push && ram_pop |-> slots_next == slots + 1)
  `BR_ASSERT_IMPL(full_a, full == (slots == 0))

endmodule : br_fifo_push_ctrl_credit
