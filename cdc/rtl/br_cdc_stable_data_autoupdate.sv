// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL Stable Data CDC with Automatic Update
//
// This is a thin wrapper around br_cdc_stable_data that generates the src_valid signal
// automatically based on whether the src_data signal has been changed.
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

    input logic dst_clk,
    input logic dst_rst,
    output logic dst_updated,
    output logic [Width-1:0] dst_data
);
  // Integration Checks
  // Rely on checks in br_cdc_stable_data submodule

  // Implementation
  logic src_valid;
  logic [Width-1:0] src_data_reg;

  `BR_REGLIX(src_data_reg, src_data, src_valid, InitValue, src_clk, src_rst)

  assign src_valid = src_data != src_data_reg;

  br_cdc_stable_data #(
      .Width(Width),
      .InitValue(InitValue),
      .RegisterResetActive(RegisterResetActive),
      .NumSyncStages(NumSyncStages)
  ) br_cdc_stable_data_inst (
      .src_clk,
      .src_rst,
      .src_valid,
      .src_data,
      .dst_clk,
      .dst_rst,
      .dst_updated,
      .dst_data
  );

  // Implementation checks
  // Rely on checks in br_cdc_stable_data submodule

endmodule : br_cdc_stable_data_autoupdate
