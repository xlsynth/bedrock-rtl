// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Test Rate Control
//
// Simple testbench helper that generates a throttled `drive` signal based on a `Rate`
// parameter.
//
// After reset, the module waits InitialDelay cycles before becoming active.
// When enabled, it asserts `drive` with probability Rate (0.0–1.0) whenever idle.
// Once asserted, `drive` remains high until acknowledged via `ack`.

`include "br_registers.svh"
`include "br_asserts.svh"

module br_test_rate_control #(
    parameter real Rate = 1.0,  // Rate between 0.0 and 1.0 inclusive
    parameter int InitialDelay = 0,  // Number of cycles to wait before becoming active
    parameter int Seed = 1  // Seed for the random number generator
) (
    input logic clk,
    input logic rst,
    input logic enable,
    output logic drive,
    input logic ack  // no effect when drive is 0
);

  `BR_ASSERT_STATIC(rate_between_zero_and_one_a, Rate >= 0.0 && Rate <= 1.0)

  // Initialize random number seed
  initial begin
    void'($urandom(Seed));
  end

  // Initial delay before the interface becomes active
  logic initial_delay_done;
  if (InitialDelay == 0) begin : gen_no_initial_delay
    assign initial_delay_done = 1'b1;
  end else begin : gen_initial_delay
    logic [$clog2(InitialDelay+1)-1:0] initial_delay_count;
    `BR_REGL(initial_delay_count, initial_delay_count + 1, !initial_delay_done)
    assign initial_delay_done = (initial_delay_count == InitialDelay);
  end

  // Pseudo-random activation with hold-until-accepted semantics
  logic drive_internal;

  always_ff @(posedge clk) begin
    if (rst) begin
      drive_internal <= 1'b0;
    end else if (!drive_internal || ack) begin
      drive_internal <= (($urandom() / $pow(2.0, 32.0)) < Rate);
    end
  end

  assign drive = (enable && initial_delay_done) ? drive_internal : 1'b0;

endmodule
