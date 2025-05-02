// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// A crappy testbench generated with o1-preview

`timescale 1ns / 1ps

module br_counter_decr_tb;

  // Parameters matching the module under test
  parameter int MaxValue = 10;  // Example maximum value
  parameter int MaxDecrement = 3;  // Example maximum change
  parameter bit EnableSaturate = 0;
  parameter bit EnableReinitAndDecr = 0;
  localparam int ValueWidth = $clog2(MaxValue + 1);
  localparam int DecrementWidth = $clog2(MaxDecrement + 1);

  // Testbench signals
  logic                      clk;
  logic                      rst;
  logic                      reinit;
  logic [    ValueWidth-1:0] initial_value;
  logic                      decr_valid;
  logic [DecrementWidth-1:0] decr;
  logic [    ValueWidth-1:0] value;
  logic [    ValueWidth-1:0] value_next;

  // Instantiate the design under test (DUT)
  br_counter_decr #(
      .ValueWidth(ValueWidth),
      .DecrementWidth(DecrementWidth),
      .MaxValue(MaxValue),
      .MaxDecrement(MaxDecrement),
      .EnableSaturate(EnableSaturate),
      .EnableReinitAndDecr(EnableReinitAndDecr)
  ) dut (
      .clk(clk),
      .rst(rst),
      .reinit(reinit),
      .initial_value(initial_value),
      .decr_valid,
      .decr,
      .value(value),
      .value_next(value_next)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic set_initial_value(int value);
    reinit = 1;
    initial_value = value;
    td.wait_cycles();
    reinit = 0;
  endtask

  // Test sequence
  initial begin
    int expected_value;

    // Initialize signals
    reinit        = 0;
    initial_value = 0;
    decr_valid    = 0;
    decr          = 0;

    // Apply reset
    td.reset_dut();

    // Wait for reset to propagate
    td.wait_cycles();

    // Test reinitialization without change
    reinit        = 1;
    initial_value = MaxValue;
    td.wait_cycles();
    reinit = 0;

    td.check_integer(value, MaxValue, "Reinit w/o Decrement mismatch");

    // Test normal decrement
    td.wait_cycles();
    set_initial_value(3);
    decr_valid = 1;
    decr = 1;

    td.wait_cycles();
    decr_valid = 0;
    td.check_integer(value, 2, "Simple decrement value mismatch");

    // Test decrementing from MaxValue to 0 by 1
    td.wait_cycles();
    set_initial_value(MaxValue);

    repeat (MaxValue) begin
      decr_valid = 1;
      decr = 1;
      td.wait_cycles();
    end

    decr_valid = 0;
    td.check_integer(value, 0, "Decrement by 1 value mismatch");

    // Test underflow wrapping / saturating
    td.wait_cycles();
    set_initial_value(0);

    decr_valid = 1;
    decr = 1;

    td.wait_cycles();
    decr_valid = 0;

    expected_value = EnableSaturate ? 0 : MaxValue;

    td.check_integer(value, expected_value, "Underflow value mismatch");

    // Test decrement during reinit
    td.wait_cycles();
    reinit = 1;
    initial_value = 5;
    decr_valid = 1;
    decr = 1;

    td.wait_cycles();
    reinit = 0;
    decr_valid = 0;

    expected_value = EnableReinitAndDecr ? 4 : 5;

    td.check_integer(value, expected_value, "Reinit w/ decrement value mismatch");

    // Finish simulation
    td.wait_cycles();
    td.finish();
  end

endmodule
