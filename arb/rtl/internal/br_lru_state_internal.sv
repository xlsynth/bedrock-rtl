// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Least-Recently-Used (LRU) State
//
// Maintains a pairwise priority matrix. state[i][j] is high when requester i
// has higher priority than requester j. The diagonal is unused and tied low.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_lru_state_internal #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,  // Synchronous active-high
    input logic update_priority,
    input logic [NumRequesters-1:0] grant,
    output logic [NumRequesters-1:0][NumRequesters-1:0] state
);

  `BR_ASSERT_STATIC(num_requesters_gte_2_A, NumRequesters >= 2)

  // We only need to maintain the upper triangular state (exclusive of
  // diagonal) in registers because the lower triangle is its complement.
  // There are NumRequesters * (NumRequesters - 1) / 2 flip-flops of priority state.
  logic [NumRequesters-1:0][NumRequesters-1:0] state_reg;
  logic [NumRequesters-1:0][NumRequesters-1:0] state_reg_next;

  for (genvar i = 0; i < NumRequesters; i++) begin : gen_state_row
    for (genvar j = 0; j < NumRequesters; j++) begin : gen_state_col
      // Upper triangle
      if (i < j) begin : gen_upper_tri
        // All bits in upper triangle init to 1'b1 (lowest numbered req wins)
        assign state_reg_next[i][j] = grant[i] ? 1'b0 : grant[j] ? 1'b1 : state[i][j];
        `BR_REGLI(state_reg[i][j], state_reg_next[i][j], update_priority, 1'b1)
        assign state[i][j] = state_reg[i][j];

        // Lower triangle is the inverse of upper triangle
      end else if (i > j) begin : gen_lower_tri
        assign state[i][j] = !state_reg[j][i];

        // Tie-off unused signals
        assign state_reg_next[i][j] = 1'b0;  // ri lint_check_waive CONST_ASSIGN
        assign state_reg[i][j] = 1'b0;  // ri lint_check_waive CONST_ASSIGN
        `BR_UNUSED_NAMED(states, {state_reg_next[i][j], state_reg[i][j]})

        // The diagonal is unused. Tie off signals.
      end else begin : gen_diag
        // ri lint_check_waive CONST_ASSIGN
        assign {state_reg_next[i][j], state_reg[i][j], state[i][j]} = '0;
        `BR_UNUSED_NAMED(states, {state_reg_next[i][j], state_reg[i][j], state[i][j]})
      end
    end
  end

  `BR_ASSERT_IMPL(grant_onehot_A, update_priority |-> $onehot(grant))
  `BR_ASSERT_IMPL(no_update_stable_A, !update_priority |=> $stable(state))

endmodule : br_lru_state_internal
