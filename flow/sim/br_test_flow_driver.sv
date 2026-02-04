// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Test Flow Driver
//
// Testbench module that drives a ready/valid data flow.
//
// After an optional startup delay, probabilistically asserts `pop_valid` based on `Rate`,
// then holds `pop_valid` high until accepted by `pop_ready`. Data is either an internally
// generated counter pattern or pulled from the provided `test_data` array.
//
// Stops driving valid and asserts `done` after `NumValues` transfers.

`include "br_registers.svh"

module br_test_flow_driver #(
    parameter int Width = 8,
    parameter bit UseCounterPattern = 1,
    parameter int NumValues = 8,
    parameter real Rate = 1.0,  // probability of asserting pop_valid on an idle cycle [0.0 - 1.0]
    parameter int InitialDelay = 10,
    parameter int Seed = 1  // seed for the random number generator
) (
    input logic clk,
    input logic rst,

    input logic [NumValues-1:0][Width-1:0] test_data,  // only used if UseCounterPattern is 0

    input  logic             pop_ready,
    output logic             pop_valid,
    output logic [Width-1:0] pop_data,

    output logic done
);

  br_test_rate_control #(
      .Rate(Rate),
      .InitialDelay(InitialDelay),
      .Seed(Seed)
  ) br_test_rate_control (
      .clk,
      .rst,
      .enable(!done),
      .drive(pop_valid),  // deasserted when done
      .ack(pop_ready)
  );

  logic popped;
  assign popped = pop_valid && pop_ready;

  localparam int CountWidth = $clog2(NumValues + 1);
  logic [CountWidth-1:0] count;
  `BR_REGL(count, count + 1, popped)
  assign done = count >= NumValues;

  logic [Width-1:0] pop_data_internal;
  assign pop_data_internal = (UseCounterPattern) ? Width'(count) :
                             (count < NumValues) ? test_data[count] : 'x;

  assign pop_data = pop_valid ? pop_data_internal : 'x;

endmodule
