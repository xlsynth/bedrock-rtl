// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL FIFO Push Controller (Credit/Valid)

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_fifo_push_ctrl_credit #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 0,
    parameter int MaxCredit = Depth,
    parameter bit RegisterPushOutputs = 0,
    parameter int RamDepth = Depth,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, cover that credit_withhold can be non-zero.
    // Otherwise, assert that it is always zero.
    parameter bit EnableCoverCreditWithhold = 1,
    // If 1, cover that push_sender_in_reset can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushSenderInReset = 1,
    // If 1, cover that push_credit_stall can be asserted
    // Otherwise, assert that it is never asserted.
    parameter bit EnableCoverPushCreditStall = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = br_math::clamped_clog2(RamDepth),
    localparam int CountWidth = $clog2(Depth + 1),
    localparam int CreditWidth = $clog2(MaxCredit + 1)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    input  logic             push_sender_in_reset,
    output logic             push_receiver_in_reset,
    input  logic             push_credit_stall,
    output logic             push_credit,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Push-side status flags
    output logic                  full,
    output logic                  full_next,
    output logic [CountWidth-1:0] slots,
    output logic [CountWidth-1:0] slots_next,

    // Push-side credits
    input  logic [CreditWidth-1:0] credit_initial_push,
    input  logic [CreditWidth-1:0] credit_withhold_push,
    output logic [CreditWidth-1:0] credit_count_push,
    output logic [CreditWidth-1:0] credit_available_push,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waiver.
    input logic bypass_ready,  // ri lint_check_waive INEFFECTIVE_NET
    output logic bypass_valid_unstable,
    output logic [Width-1:0] bypass_data_unstable,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,

    // Internal handshakes between push and pop controllers
    output logic push_beat,
    input  logic pop_beat
);

  logic either_rst;
  assign either_rst = rst || push_sender_in_reset;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 2)
  `BR_ASSERT_STATIC(bit_width_must_be_at_least_one_a, Width >= 1)
  `BR_ASSERT_STATIC(credit_width_a, CreditWidth >= $clog2(Depth + 1))

  `BR_COVER_CR_INTG(full_c, full, clk, either_rst)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  logic internal_valid;
  logic [Width-1:0] internal_data;

  br_credit_receiver #(
      .Width                       (Width),
      .MaxCredit                   (MaxCredit),
      .RegisterPushOutputs         (RegisterPushOutputs),
      .EnableCoverCreditWithhold   (EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall  (EnableCoverPushCreditStall),
      .EnableAssertFinalNotValid   (EnableAssertFinalNotValid)
  ) br_credit_receiver (
      .clk,
      // Not using either_rst here so that there is no path from
      // push_sender_in_reset to push_receiver_in_reset.
      .rst,
      .push_sender_in_reset,
      .push_receiver_in_reset,
      .push_credit_stall(push_credit_stall),
      .push_credit(push_credit),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_credit(pop_beat),
      .pop_valid(internal_valid),
      .pop_data(internal_data),
      .credit_initial(credit_initial_push),
      .credit_withhold(credit_withhold_push),
      .credit_count(credit_count_push),
      .credit_available(credit_available_push)
  );

  // Core flow-control logic

  logic [AddrWidth-1:0] addr_base;
  logic [AddrWidth-1:0] addr_bound;

  assign addr_base  = '0;
  assign addr_bound = RamDepth - 1;

  br_fifo_push_ctrl_core #(
      .Depth(RamDepth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      // The core push control should never be backpressured.
      .EnableCoverPushBackpressure(0),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_fifo_push_ctrl_core (
      .clk,
      .rst(either_rst),

      .addr_base,
      .addr_bound,

      .push_ready(),
      .push_valid(internal_valid),
      .push_data (internal_data),

      .bypass_ready,
      .bypass_valid_unstable,  // ri lint_check_waive CONST_OUTPUT
      .bypass_data_unstable,  // ri lint_check_waive CONST_OUTPUT

      .ram_wr_valid,
      .ram_wr_addr_next(),
      .ram_wr_addr,
      .ram_wr_data,

      .full,
      .push_beat
  );

  // Status flags
  br_counter #(
      .MaxValue(Depth),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableWrap(0),
      .EnableCoverZeroChange(0),
      .EnableCoverReinit(0)
  ) br_counter_slots (
      .clk,
      .rst(either_rst),

      .reinit(1'b0),
      .initial_value(CountWidth'($unsigned(Depth))),

      .incr_valid(pop_beat),
      .incr      (1'b1),

      .decr_valid(push_beat),
      .decr      (1'b1),

      .value     (slots),
      .value_next(slots_next)
  );

  assign full_next = slots_next == 0;
  `BR_REGLX(full, full_next, push_beat || pop_beat, clk, either_rst)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_CR_IMPL(ram_wr_addr_in_range_a, ram_wr_valid |-> ram_wr_addr < RamDepth, clk,
                     either_rst)

  // Flow control and latency
  `BR_ASSERT_CR_IMPL(no_overflow_a, internal_valid |-> !full, clk, either_rst)
  `BR_ASSERT_CR_IMPL(ram_push_and_bypass_mutually_exclusive_a,
                     !(ram_wr_valid && bypass_ready && bypass_valid_unstable), clk, either_rst)

  // Flags
  `BR_ASSERT_CR_IMPL(slots_in_range_a, slots <= Depth, clk, either_rst)
  `BR_ASSERT_CR_IMPL(slots_next_a, ##1 slots == $past(slots_next), clk, either_rst)
  `BR_ASSERT_CR_IMPL(push_and_pop_slots_a, push_beat && pop_beat |-> slots_next == slots, clk,
                     either_rst)
  `BR_ASSERT_CR_IMPL(push_slots_a, push_beat && !pop_beat |-> slots_next == slots - 1, clk,
                     either_rst)
  `BR_ASSERT_CR_IMPL(pop_slots_a, !push_beat && pop_beat |-> slots_next == slots + 1, clk,
                     either_rst)
  `BR_ASSERT_CR_IMPL(full_a, full == (slots == 0), clk, either_rst)

endmodule : br_fifo_push_ctrl_credit
