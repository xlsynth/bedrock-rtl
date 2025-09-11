// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_cdc_bit_pulse #(
    // Number of synchronization stages. Must be at least 1.
    // WARNING: Setting this parameter correctly is critical to
    // ensuring a low probability of metastability.
    // The recommended value is 3 for most technology nodes.
    // Do not decrease below that unless you have a good reason.
    parameter int NumStages = 3,
    parameter bit RegisterOutput = 0
) (
    input logic src_clk,
    input logic src_rst,
    input logic src_pulse,

    // ri lint_check_waive ONE_LOCAL_CLOCK
    input  logic dst_clk,
    input  logic dst_rst,
    output logic dst_pulse
);
  // Integration Assertions
  // Relying on checks in br_cdc_bit_toggle

  // Implementation
  logic src_level;
  logic dst_level;
  logic dst_level_d;
  logic dst_pulse_internal;

  // Create a level signal on the source clock that toggles
  // on every pulse.
  `BR_REGLX(src_level, !src_level, src_pulse, src_clk, src_rst)

  br_cdc_bit_toggle #(
      // Don't add a source flop since src_level is already
      // a register
      .AddSourceFlop(0),
      .NumStages(NumStages)
  ) br_cdc_bit_toggle_inst (
      .src_clk,
      .src_rst,
      .src_bit(src_level),
      .dst_clk,
      .dst_rst,
      .dst_bit(dst_level)
  );

  // Recreate the pulse on the destination clock by
  // detecting edges.
  // Use a non-resetting register here to avoid a pulse
  // being spuriously generated when the destination reset
  // is asserted while the saved level is high.
  `BR_REGNX(dst_level_d, dst_level, dst_clk)

  assign dst_pulse_internal = dst_level ^ dst_level_d;

  if (RegisterOutput) begin : gen_register_output
    `BR_REGX(dst_pulse, dst_pulse_internal, dst_clk, dst_rst)
  end else begin : gen_no_register_output
    assign dst_pulse = dst_pulse_internal;
  end

  // Implementation assertions
  // TODO(zhemao): Add some here

endmodule
