// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fibonacci LFSR
//
// With appropriate choice of taps (see br_lfsr_taps package), the LFSR
// produces a maximal period of 2^Width - 1. Both single bit and full state
// outputs are provided. The single bit output is the LSB of the state and,
// for a maximal period LFSR, is nearly equidistributed between 0 and 1. (A
// maximal period has an odd length and contains one more 1 output than 0
// output.) The full state output is the current state of the LFSR. For a
// maximal period LFSR, each state in [1, 2^Width-1] is visited exactly
// once during the period.
//
// See the br_lfsr_taps package for the taps that produce maximum-length LFSRs
// of given widths.
//
// The Fibonacci LFSR is implemented using a shift register. The next state
// is computed by ANDing current state with taps and XOR reducing the result
// to a single bit. This "feedback" value becomes the LSB of the new state.
// The remaining bits of the state are the previous state left shifted by 1 bit
// with the MSB discarded. With appropriate choice of taps (see br_lfsr_taps.svh),
// MSB discarded.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_lfsr #(
    // Width of the LFSR state. Must be at least 2.
    parameter int Width = 2,
    // Number of LFSR state update steps per advance. If AdvanceSteps is relatively
    // prime to the period of the LFSR, then advancing multiple steps does not change
    // the period of the resulting LFSR. Higher values of AdvanceSteps result in more
    // "state mixing" per advance.
    parameter int AdvanceSteps = 1,
    // Enable check that MSB of taps is set. This is necessary, but not sufficient,
    // for a maximal period LFSR. Disabling this checks allows the LFSR to be used
    // more flexibly (e.g. supporting adjustable period LFSRs by changing the taps).
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertTapsMsbIsSet = 1,
    // Enable check that initial state is non-zero. If the LFSR is initialized to zero,
    // it will never advance and the output will be zero forever. Generally, this is not
    // the behavior intended, but may be useful to support "disabling" the LFSR.
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAssertInitialStateNonZero = 1
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,
    // Reinitialize the LFSR to initial_state.
    input logic reinit,
    // Initial state of the LFSR (for reset and reinit)
    input logic [Width-1:0] initial_state,
    // Taps for the LFSR.
    input logic [Width-1:0] taps,
    // Advances the LFSR state
    input logic advance,
    // LSB of the LFSR state
    output logic out,
    // The full state of the LFSR
    output logic [Width-1:0] out_state
);
  //------------------------------------------
  // Integration checks
  //------------------------------------------
  localparam longint AdvanceStepsPlusTwo = (AdvanceSteps > 0) ? longint'(AdvanceSteps) + 2 : 2;

  `BR_ASSERT_STATIC(width_gte_two_a, Width >= 2)
  `BR_ASSERT_STATIC(advance_steps_gt_zero_a, AdvanceSteps > 0)
  // Equivalent to AdvanceSteps < 2**Width - 1, but avoids constructing 2**Width.
  `BR_ASSERT_STATIC(advance_steps_lt_period_a, $clog2(AdvanceStepsPlusTwo) <= Width)
  if (EnableAssertTapsMsbIsSet) begin : gen_taps_msb_check
    `BR_ASSERT_INTG(taps_msb_set_a, taps[Width-1] == 1'b1)
  end
  if (EnableAssertInitialStateNonZero) begin : gen_initial_state_check
    `BR_ASSERT_INTG(initial_state_non_zero_a, initial_state != '0)
  end

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [Width-1:0] state;
  logic [Width-1:0] next_state;

  function automatic logic [Width-1:0] get_next_state(input logic [Width-1:0] current_state,
                                                      input logic [Width-1:0] current_taps);
    logic [Width-1:0] advanced_state;

    advanced_state = current_state;
    // ri lint_check_waive LOOP_VAR_NOT_USED
    for (int i = 0; i < AdvanceSteps; i++) begin
      advanced_state = {advanced_state[Width-2:0], ^(advanced_state & current_taps)};
    end
    return advanced_state;
  endfunction

  assign out = state[0];
  assign out_state = state;
  assign next_state = reinit ? initial_state : get_next_state(state, taps);

  `BR_REGLI(state, next_state, advance || reinit, initial_state)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  if (EnableAssertInitialStateNonZero) begin : gen_out_state_non_zero_check
    `BR_ASSERT_IMPL(out_state_non_zero_a, out_state != '0)
    // Assumes AdvanceSteps is not equal to the LFSR period.
    `BR_ASSERT_IMPL(advance_changes_a, advance && !reinit |=> out_state != $past(out_state))
  end else begin : gen_out_state_zero_check
    `BR_ASSERT_IMPL(out_state_zero_a, out_state == '0)
  end
  `BR_ASSERT_IMPL(no_advance_holds_a, !advance && !reinit |=> (out_state == $past(out_state)
                                      ) && (out == $past(out)))

  // Reinit
  `BR_COVER_IMPL(reinit_c, reinit)
  `BR_COVER_IMPL(reinit_and_advance_c, reinit && advance)

endmodule
