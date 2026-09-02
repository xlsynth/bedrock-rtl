// SPDX-License-Identifier: Apache-2.0

`include "br_registers.svh"

// Elaborate every NOSCAN macro with scalar and vector ports and explicit clocks/resets.
module br_registers_noscan_test (
    input logic reg_clk,
    input logic sync_rst,
    input logic async_rst,
    input logic en,
    input logic scalar_d,
    input logic [7:0] vector_d,
    output logic no_reset_scalar,
    output logic sync_scalar,
    output logic sync_en_scalar,
    output logic async_scalar,
    output logic async_en_scalar,
    output logic [7:0] no_reset_vector,
    output logic [7:0] sync_vector,
    output logic [7:0] sync_en_vector,
    output logic [7:0] async_vector,
    output logic [7:0] async_en_vector
);

  // Custom names intentionally exercise the explicit clock/reset arguments.
  // ri lint_check_off SAME_CLOCK_NAME SAME_RESET_NAME
  `BR_REGNX_NOSCAN(no_reset_scalar, scalar_d, reg_clk)
  `BR_REGX_NOSCAN(sync_scalar, scalar_d, reg_clk, sync_rst)
  `BR_REGLX_NOSCAN(sync_en_scalar, scalar_d, en, reg_clk, sync_rst)
  `BR_REGAX_NOSCAN(async_scalar, scalar_d, reg_clk, async_rst)
  `BR_REGALX_NOSCAN(async_en_scalar, scalar_d, en, reg_clk, async_rst)

  `BR_REGNX_NOSCAN(no_reset_vector, vector_d, reg_clk)
  `BR_REGX_NOSCAN(sync_vector, vector_d, reg_clk, sync_rst)
  `BR_REGLX_NOSCAN(sync_en_vector, vector_d, en, reg_clk, sync_rst)
  `BR_REGAX_NOSCAN(async_vector, vector_d, reg_clk, async_rst)
  `BR_REGALX_NOSCAN(async_en_vector, vector_d, en, reg_clk, async_rst)
  // ri lint_check_on SAME_CLOCK_NAME SAME_RESET_NAME

endmodule : br_registers_noscan_test
