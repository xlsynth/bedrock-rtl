// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Multicycle Path Marker
//
// Identifies a path as multicycle and adds assertions. The primary use of
// this is for constraint generation and design verification. This does not
// add any logic.
//
// To automatically instantiate this at the width of local logic,
// users can opt to use the convenience macros defined in macros/br_multicycle_path.svh.

`include "br_asserts_internal.svh"

module br_misc_multicycle_path #(
    parameter int Cycles = 2,  // Should be at least 1
    parameter int Width = 1,  // Must be at least 1
    parameter int AllowChangesOnlyInReset = 0
) (
    // Positive edge-triggered. Only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    // Synchronous active-high. Only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic rst,

    input  logic [Width-1:0] in,
    output logic [Width-1:0] out
);

  `BR_ASSERT_STATIC(cycles_gte_1, Cycles >= 1)
  `BR_ASSERT_STATIC(width_gte_1, Width >= 1)
  `BR_ASSERT_STATIC(allow_changes_only_in_reset_legal,
                    (AllowChangesOnlyInReset == 0) || (AllowChangesOnlyInReset == 1))

  generate
    if (AllowChangesOnlyInReset) begin : gen_input_constraints
      `BR_ASSERT_INTG(in_stable_outside_reset_a, in == $past(in))
    end : gen_input_constraints
  endgenerate

  assign out = in;

endmodule : br_misc_multicycle_path
