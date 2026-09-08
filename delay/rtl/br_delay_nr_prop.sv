// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Delay Line (No Reset, With Output-Known Assertion)
//
// Wraps br_delay_nr and asserts that out contains no X/Z when downstream
// logic is out of reset. Hold rst high until out can be consumed.
// The rst input only controls the assertion; it never resets the registers.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

module br_delay_nr_prop #(
    parameter int Width = 1,  // Must be at least 1
    parameter int NumStages = 0  // Must be at least 0
) (
    // Positive edge-triggered. If NumStages is 0, then only used for assertions.
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input  logic                          clk,
    // Synchronous active-high reset of the output consumer, used only for the assertion.
    input  logic                          rst,
    input  logic [  Width-1:0]            in,
    // Output of last delay stage (delayed by NumStages cycles).
    output logic [  Width-1:0]            out,
    // Output of each delay stage. Note that out_stages[0] == in, and
    // out_stages[NumStages] == out.
    output logic [NumStages:0][Width-1:0] out_stages
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_KNOWN_INTG(out_known_a, out)
  // rst is only used for the integration check.
  `BR_UNUSED(rst)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  br_delay_nr #(
      .Width(Width),
      .NumStages(NumStages)
  ) br_delay_nr (
      .clk,
      .in,
      .out,
      .out_stages
  );

endmodule : br_delay_nr_prop
