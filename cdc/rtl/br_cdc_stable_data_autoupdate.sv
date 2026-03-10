// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Stable Data CDC with Automatic Update
//
// This is a thin wrapper around br_cdc_reg for synchronizing an infrequently
// changing multi-bit value. It is similar to br_cdc_stable_data, but the src_valid
// signal is generated automatically based on whether the src_data signal has been changed.
//

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_cdc_stable_data_autoupdate #(
    parameter int Width = 1,
    parameter logic [Width-1:0] InitValue = '0,
    parameter bit RegisterResetActive = 1,
    parameter int NumSyncStages = 3
) (
    input logic src_clk,
    input logic src_rst,
    input logic [Width-1:0] src_data,

    // ri lint_check_waive ONE_LOCAL_CLOCK
    input logic dst_clk,
    input logic dst_rst,
    output logic dst_updated,
    output logic [Width-1:0] dst_data
);
  // Integration Checks
  // Rely on checks in br_cdc_stable_data submodule

  // Implementation
  logic src_valid;
  logic src_ready;
  logic [Width-1:0] src_data_reg;

  logic dst_updated_next;
  logic [Width-1:0] dst_data_next;

  `BR_REGLIX(src_data_reg, src_data, src_valid && src_ready, InitValue, src_clk, src_rst)

  // Send into the register if the data has changed but hasn't been
  // crossed over yet.
  assign src_valid = src_data != src_data_reg;

  br_cdc_reg #(
      .Width(Width),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages),
      // Data can change if data changes while register is backpressured
      .EnableAssertPushDataStability(0)
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

  // Implementation checks
  // TODO(zhemao): Add some here

endmodule : br_cdc_stable_data_autoupdate
