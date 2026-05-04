// SPDX-License-Identifier: Apache-2.0
//
// FPV repro for zero-decrement ready behavior.

`include "br_asserts.svh"

module br_credit_counter_zero_decr_ready_fpv_repro (
    input logic clk,
    input logic rst
);
  localparam int MaxValue = 1;
  localparam int MaxChange = 1;
  localparam int ValueWidth = $clog2(MaxValue + 1);
  localparam int ChangeWidth = $clog2(MaxChange + 1);

  logic incr_valid;
  logic [ChangeWidth-1:0] incr;
  logic decr_ready;
  logic decr_valid;
  logic [ChangeWidth-1:0] decr;
  logic [ValueWidth-1:0] initial_value;
  logic [ValueWidth-1:0] withhold;
  logic [ValueWidth-1:0] value;
  logic [ValueWidth-1:0] available;

  br_credit_counter #(
      .MaxValue(MaxValue),
      .MaxChange(MaxChange)
  ) dut (
      .clk,
      .rst,
      .incr_valid,
      .incr,
      .decr_ready,
      .decr_valid,
      .decr,
      .initial_value,
      .withhold,
      .value,
      .available
  );

  assign initial_value = '0;
  assign withhold = '0;
  assign incr_valid = 1'b0;
  assign incr = '0;
  assign decr_valid = !rst;
  assign decr = '0;

  `BR_ASSERT(zero_decr_ready_a, !rst && decr_valid && decr == '0 && available == '0 |->
             decr_ready)
  `BR_ASSERT(zero_decr_keeps_value_a, !rst && decr_valid && decr_ready && decr == '0 |=>
             value == $past(value))

endmodule : br_credit_counter_zero_decr_ready_fpv_repro
