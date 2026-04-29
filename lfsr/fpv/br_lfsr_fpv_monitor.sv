// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fibonacci LFSR Formal Monitor
//
// This monitor checks that a configured maximum-length LFSR stays out of the
// all-zero lock-up state, preserves state while stalled, reloads initial_state
// on reinit, and does not repeat an out_state value within one expected period.
// The period check constrains taps to the known-good table values for the
// selected Width and compares two arbitrary positions in the cycle.

`include "br_asserts.svh"
`include "br_fv.svh"
`include "br_registers.svh"

module br_lfsr_fpv_monitor #(
    parameter int Width = 2,
    parameter bit EnableAssertTapsMsbIsSet = 1,
    parameter bit EnableAssertInitialStateNonZero = 1,
    localparam int Period = (2 ** Width) - 1,
    localparam int PeriodCounterWidth = $clog2(Period)
) (
    input logic             clk,
    input logic             rst,
    input logic             reinit,
    input logic [Width-1:0] initial_state,
    input logic [Width-1:0] taps,
    input logic             advance,
    input logic             out,
    input logic [Width-1:0] out_state
);

  `BR_ASSERT_STATIC(width_gte_two_a, Width >= 2)
  `BR_ASSERT_STATIC(width_supported_a, Width <= 16)

  function automatic logic [Width-1:0] get_expected_taps();
    if (Width == 2) begin
      return br_lfsr_taps::TapsWidth2;
    end else if (Width == 3) begin
      return br_lfsr_taps::TapsWidth3;
    end else if (Width == 4) begin
      return br_lfsr_taps::TapsWidth4;
    end else if (Width == 5) begin
      return br_lfsr_taps::TapsWidth5;
    end else if (Width == 6) begin
      return br_lfsr_taps::TapsWidth6;
    end else if (Width == 7) begin
      return br_lfsr_taps::TapsWidth7;
    end else if (Width == 8) begin
      return br_lfsr_taps::TapsWidth8;
    end else if (Width == 9) begin
      return br_lfsr_taps::TapsWidth9;
    end else if (Width == 10) begin
      return br_lfsr_taps::TapsWidth10;
    end else if (Width == 11) begin
      return br_lfsr_taps::TapsWidth11;
    end else if (Width == 12) begin
      return br_lfsr_taps::TapsWidth12;
    end else if (Width == 13) begin
      return br_lfsr_taps::TapsWidth13;
    end else if (Width == 14) begin
      return br_lfsr_taps::TapsWidth14;
    end else if (Width == 15) begin
      return br_lfsr_taps::TapsWidth15;
    end else begin
      return br_lfsr_taps::TapsWidth16;
    end
  endfunction

  //------------------------------------------
  // Assumptions
  //------------------------------------------

  `BR_ASSUME(initial_state_non_zero_a, initial_state != '0)
  `BR_ASSUME(initial_state_stable_a, $stable(initial_state))
  `BR_ASSUME(taps_known_good_a, taps == get_expected_taps())
  `BR_ASSUME(taps_stable_a, $stable(taps))

  //------------------------------------------
  // Local behavior checks
  //------------------------------------------

  `BR_ASSERT(out_check_a, out == out_state[0])
  `BR_ASSERT(out_state_non_zero_a, out_state != '0)
  `BR_ASSERT(no_advance_holds_a, !advance && !reinit |=> out_state == $past(out_state))
  `BR_ASSERT(reinit_loads_initial_state_a, reinit |=> out_state == $past(initial_state))

  //------------------------------------------
  // Full-period checks
  //------------------------------------------

  logic [PeriodCounterWidth-1:0] period_count;
  logic                          period_done;
  logic [PeriodCounterWidth-1:0] state_a;
  logic [PeriodCounterWidth-1:0] state_b;
  logic [             Width-1:0] out_state_a;

  `BR_FV_2RAND_IDX(state_a, state_b, Period)
  `BR_ASSUME(state_a_lt_state_b_a, state_a < state_b)

  // Pick two arbitrary positions in the expected period. Capture the out_state
  // at the earlier position and check that the later position differs.
  always_ff @(posedge clk) begin
    if (rst || reinit) begin
      period_count <= '0;
      period_done  <= 1'b0;
      out_state_a  <= '0;
    end else begin
      if (period_count == state_a) begin
        out_state_a <= out_state;
      end

      if (advance) begin
        if (period_count == PeriodCounterWidth'(Period - 1)) begin
          period_count <= '0;
          period_done  <= 1'b1;
        end else begin
          period_count <= period_count + 1'b1;
        end
      end
    end
  end

  // Since state_a and state_b are arbitrary distinct period positions, this
  // proves any two positions in the period produce different LFSR states.
  `BR_ASSERT(no_duplicate_states_a, period_count == state_b |-> out_state_a != out_state)

  `BR_COVER(full_period_done_c, period_done)

endmodule : br_lfsr_fpv_monitor

bind br_lfsr br_lfsr_fpv_monitor #(
    .Width(Width),
    .EnableAssertTapsMsbIsSet(EnableAssertTapsMsbIsSet),
    .EnableAssertInitialStateNonZero(EnableAssertInitialStateNonZero)
) monitor (.*);
