// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Stable Data CDC
//
// This is a thin wrapper around br_cdc_reg for synchronizing an infrequently
// changing multi-bit value. The register updates with the value of src_data
// when src_valid is asserted and holds the value on dst_data until the next time
// src_valid is asserted.
//

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_cdc_stable_data #(
    parameter int Width = 1,  // Must be at least 1
    // The initial value of the destination-side register.
    // dst_data will hold this value until the first time src_valid=1
    parameter logic [Width-1:0] InitValue = '0,
    // If 1 (the default), register push_rst on push_clk and pop_rst on pop_clk
    // before sending to the CDC synchronizers. This adds one cycle to the cut-through
    // latency and one cycle to the backpressure latency.
    // Do not set this to 0 unless push_rst and pop_rst are driven directly by
    // registers.
    parameter bit RegisterResetActive = 1,
    // Number of synchronization stages to use. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumSyncStages = 3
) (
    input logic src_clk,
    input logic src_rst,
    input logic src_valid,
    input logic [Width-1:0] src_data,

    input logic dst_clk,
    input logic dst_rst,
    output logic dst_updated,
    output logic [Width-1:0] dst_data
);
  // Integration Checks
  // Only used for assertion
  logic src_ready;

  // Rely on submodules for static parameter checks

  `BR_ASSERT_CR_INTG(no_reg_overflow_A, src_valid |-> src_ready, src_clk, src_rst)

  // Implementation
  logic dst_updated_next;
  logic [Width-1:0] dst_data_next;

  br_cdc_reg #(
      .Width(Width),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages),
      // There shouldn't be push backpressure
      .EnableCoverPushBackpressure(0)
  ) br_cdc_reg_inst (
      .push_clk  (src_clk),    // ri lint_check_waive SAME_CLOCK_NAME
      .push_rst  (src_rst),
      .push_valid(src_valid),
      .push_ready(src_ready),
      .push_data (src_data),

      .pop_clk(dst_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .pop_rst(dst_rst),
      .pop_ready(1'b1),
      .pop_valid(dst_updated_next),
      .pop_data(dst_data_next)
  );

  `BR_REGX(dst_updated, dst_updated_next, dst_clk, dst_rst)
  `BR_REGLIX(dst_data, dst_data_next, dst_updated_next, InitValue, dst_clk, dst_rst)
  `BR_UNUSED(src_ready)

  // Implementation checks
  // TODO(zhemao): Add some here

endmodule
