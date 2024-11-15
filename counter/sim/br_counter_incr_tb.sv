// Copyright 2024 The Bedrock-RTL Authors
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

module br_counter_incr_tb;

  // Parameters matching the module under test
  parameter int MaxValue = 15;  // Example maximum value
  parameter int MaxIncrement = 3;  // Example maximum increment
  localparam int ValueWidth = $clog2(MaxValue + 1);
  localparam int IncrementWidth = $clog2(MaxIncrement + 1);

  // Testbench signals
  logic                      clk;
  logic                      rst;
  logic                      reinit;
  logic [    ValueWidth-1:0] initial_value;
  logic                      incr_valid;
  logic [IncrementWidth-1:0] incr;
  logic [    ValueWidth-1:0] value;
  logic [    ValueWidth-1:0] value_next;

  // Instantiate the module under test (MUT)
  br_counter_incr #(
      .MaxValue(MaxValue),
      .MaxIncrement(MaxIncrement)
  ) dut (
      .clk(clk),
      .rst(rst),
      .reinit(reinit),
      .initial_value(initial_value),
      .incr_valid(incr_valid),
      .incr(incr),
      .value(value),
      .value_next(value_next)
  );

  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;  // 100MHz clock

  // Test sequence
  integer error_count;
  initial begin
    error_count   = 0;

    // Initialize signals
    rst           = 1;
    reinit        = 0;
    initial_value = 0;
    incr_valid    = 0;
    incr          = 0;

    // Apply reset
    @(negedge clk);
    rst = 1;
    @(negedge clk);
    rst = 0;

    // Wait for reset to propagate
    @(negedge clk);

    // Test incrementing by 1 for MaxValue cycles.
    @(negedge clk);
    incr_valid = 1;
    incr       = 1;
    repeat (MaxValue) @(negedge clk);
    incr_valid = 0;
    incr       = 0;

    // Check the value
    @(negedge clk);
    if (value !== MaxValue) begin
      error_count++;
      $error("Test failed: Expected value = %0d, Got value = %0d", MaxValue, value);
    end

    // Apply reset
    @(negedge clk);
    rst = 1;
    @(negedge clk);
    rst        = 0;

    // Test incrementing by MaxIncrement
    incr_valid = 1;
    incr       = MaxIncrement;
    @(negedge clk);
    incr_valid = 0;
    incr       = 0;

    // Check the value
    @(negedge clk);
    if (value !== MaxIncrement) begin
      error_count++;
      $error("Test failed: Expected value = %0d Got value = %0d", MaxIncrement, value);
    end

    // Test reinitialization without increment
    @(negedge clk);
    reinit        = 1;
    initial_value = MaxValue;
    @(negedge clk);
    reinit = 0;

    if (value !== MaxValue) begin
      error_count++;
      $error("Test failed: Expected reinitialized value = %0d, Got value = %0d", MaxValue, value);
    end

    // Test wrapping around MaxValue
    @(negedge clk);
    incr_valid = 1;
    incr       = 1;

    @(negedge clk);
    incr_valid = 0;
    incr       = 0;
    if (value !== 0) begin
      error_count++;
      $error("Test failed: Expected wrap-around value = 0, Got value = %0d", value);
    end

    // Test reinit with increment on the same cycle
    @(negedge clk);
    reinit        = 1;
    initial_value = 2;
    incr_valid    = 1;
    incr          = 1;
    @(negedge clk);
    reinit     = 0;
    incr_valid = 0;
    incr       = 0;

    @(negedge clk);
    if (value !== 3) begin
      error_count++;
      $error("Test failed: Expected value = 3, Got value = %0d", value);
    end

    // Finish simulation
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $display("Simulation failed with %0d errors.", error_count);
    end
    $finish;
  end

endmodule
