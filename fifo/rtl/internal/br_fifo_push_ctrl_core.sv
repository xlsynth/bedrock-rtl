// SPDX-License-Identifier: Apache-2.0


// Core FIFO push control logic that will be reused across different variants.
// Contains just the bypass and RAM write logic, leaving occupancy tracking up to
// the instantiating module.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_fifo_push_ctrl_core #(
    parameter int Depth = 1,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    // If 1, cover that the push side experiences backpressure.
    // If 0, assert that there is never backpressure.
    parameter bit EnableCoverPushBackpressure = 1,
    // If 1, assert that push_valid is stable when backpressured.
    parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure,
    // If 1, assert that push_data is stable when backpressured.
    parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability,
    // If 1, assert that push_data is always known (not X) when push_valid is asserted.
    parameter bit EnableAssertPushDataKnown = 1,
    // If 1, then assert there are no valid bits asserted and that the FIFO is
    // empty at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int AddrWidth = br_math::clamped_clog2(Depth)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waiver.
    input  logic             bypass_ready,           // ri lint_check_waive INEFFECTIVE_NET
    output logic             bypass_valid_unstable,
    output logic [Width-1:0] bypass_data_unstable,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr_next,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,

    // Address base and bound configuration
    input logic [AddrWidth-1:0] addr_base,
    // addr_bound is inclusive
    input logic [AddrWidth-1:0] addr_bound,

    // Signals to/from internal logic
    input  logic full,
    output logic push_beat
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------

  `BR_ASSERT_STATIC(depth_must_be_at_least_one_a, Depth >= 1)
  `BR_ASSERT_IMPL(addr_base_lte_addr_bound_a, addr_base <= addr_bound)
  `BR_ASSERT_IMPL(addr_bound_in_range_a, addr_bound < Depth)

  br_flow_checks_valid_data_intg #(
      .NumFlows(1),
      .Width(Width),
      .EnableCoverBackpressure(EnableCoverPushBackpressure),
      .EnableAssertValidStability(EnableAssertPushValidStability),
      .EnableAssertDataStability(EnableAssertPushDataStability),
      .EnableAssertDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_flow_checks_valid_data_intg (
      .clk,
      .rst,
      .ready(push_ready),
      .valid(push_valid),
      .data (push_data)
  );

  //------------------------------------------
  // Implementation
  //------------------------------------------
  // Flow control
  assign push_beat  = push_ready && push_valid;
  assign push_ready = !full;

  // RAM path
  if (Depth > 1) begin : gen_wr_addr_counter
    logic addr_wrap;

    assign addr_wrap = ram_wr_valid && ram_wr_addr == addr_bound;

    br_counter_incr #(
        .MaxValue(Depth - 1),
        .MaxIncrement(1),
        .EnableReinitAndIncr(0),
        // There won't be any overflows since reinit will be asserted
        // when the counter wraps around.
        .EnableWrap(0),
        .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
        .EnableCoverZeroIncrement(0),
        .EnableCoverReinitNoIncr(0)
    ) br_counter_incr_wr_addr (
        .clk,
        .rst,
        .reinit(addr_wrap),
        .initial_value(addr_base),
        .incr_valid(ram_wr_valid),
        .incr(1'b1),
        .value(ram_wr_addr),
        .value_next(ram_wr_addr_next)
    );
  end else begin : gen_wr_addr_const
    assign ram_wr_addr = '0;
    assign ram_wr_addr_next = '0;
    `BR_UNUSED_NAMED(addr_base_bound, {addr_base, addr_bound})
  end

  // Datapath
  if (EnableBypass) begin : gen_bypass
    assign bypass_valid_unstable = push_valid;
    assign bypass_data_unstable = push_data;

    assign ram_wr_valid = push_beat && !bypass_ready;
    assign ram_wr_data = push_data;
  end else begin : gen_no_bypass
    `BR_UNUSED(bypass_ready)
    // TODO(zhemao, #157): Replace this with BR_TIEOFF macros once they are fixed
    assign bypass_valid_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
    assign bypass_data_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT

    assign ram_wr_valid = push_beat;
    assign ram_wr_data = push_data;
  end

endmodule
