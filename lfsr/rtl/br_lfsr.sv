// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Fibonacci LFSR
//
// With appropriate choice of taps (see br_lfsr_taps package), the LFSR
// produces a maximal period of 2^Width - 1. Both single bit and full state
// outputs are provided. The single bit output is the LSB of the state and,
// for a maximal period LFSR, is nearly equidistributed between 0 and 1. (A
// maximal period has an odd length and contains one more 1 output than 0
// output.) The full state output is the current state of the LFSR. For a
// maximal period LFSR, each state in [1, 2^(Width-1)] is visited exactly
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
    parameter int Width = 2
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
  `BR_ASSERT_STATIC(width_gte_two_a, Width >= 2)
  `BR_ASSERT_INTG(taps_msb_set_a, taps[Width-1] == 1'b1)
  `BR_ASSERT_INTG(initial_state_non_zero_a, initial_state != '0)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  logic [Width-1:0] state;
  logic [Width-1:0] next_state;

  assign out = state[0];
  assign out_state = state;
  assign next_state = reinit ? initial_state : {state[Width-2:0], ^(state & taps)};

  `BR_REGLI(state, next_state, advance || reinit, initial_state)

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

  // Value
  `BR_ASSERT_IMPL(out_state_non_zero_a, out_state != '0)
  `BR_ASSERT_IMPL(advance_changes_a, advance |=> out_state != $past(out_state))
  `BR_ASSERT_IMPL(no_advance_holds_a, !advance |=> (out_state == $past(out_state)) && (out == $past
                                      (out)))

  // Reinit
  `BR_COVER_IMPL(reinit_c, reinit)
  `BR_COVER_IMPL(reinit_and_advance_c, reinit && advance)

endmodule
