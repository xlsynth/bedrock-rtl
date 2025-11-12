// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL CDC Reset Synchronizer
//
// A high-asserted asynchronous reset signal is synchronized to a synchronous
// reset signal.

`include "br_asserts.svh"
`include "br_gates.svh"

module br_cdc_rst_sync #(
    parameter int NumStages = 3  // must be at least 1
) (
    input  logic clk,
    input  logic arst,  // active-high async reset
    output logic srst   // active high sync reset
);

  `BR_ASSERT_STATIC(num_stages_must_be_at_least_1_a, NumStages >= 1)

  logic srst_n;

  // Instantiate a synchronizer with an async reset
  // ri lint_check_waive RESET_LEVEL CONST_FF ONE_CONN_PER_LINE RESET_DRIVER
  `BR_GATE_CDC_SYNC_ARST_STAGES(srst_n, 1'b1, clk, arst, NumStages)

  // The reset value of the synchronizer is 0, so we need to invert the output
  // ri lint_check_waive ONE_CONN_PER_LINE SAME_RESET_NAME
  `BR_GATE_INV(srst, srst_n)

endmodule : br_cdc_rst_sync
