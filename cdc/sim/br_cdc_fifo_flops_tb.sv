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

`timescale 1ns / 1ps

module br_cdc_fifo_flops_tb;

  // Parameters
  parameter int Depth = 13;
  parameter int Width = 8;
  parameter int RegisterPopOutputs = 0;
  parameter int FlopRamAddressDepthStages = 0;
  parameter int FlopRamReadDataDepthStages = 0;
  parameter int NumSyncStages = 3;

  // Clock and Reset
  // Same clock for both push and pop side for now
  // TODO(zhemao): Test with different push and pop frequencies
  reg clk;
  reg rst;

  logic start;
  logic finished;
  logic [31:0] error_count;

  // Push Interface
  wire push_ready;
  reg push_valid;
  reg [Width-1:0] push_data;

  // Pop Interface
  reg pop_ready;
  wire pop_valid;
  wire [Width-1:0] pop_data;

  // Status Outputs
  wire empty;
  wire full;
  wire [$clog2(Depth+1)-1:0] items;
  wire [$clog2(Depth+1)-1:0] slots;

  // Instantiate the FIFO
  br_cdc_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages)
  ) dut (
      .push_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .push_rst(rst),
      .push_ready,
      .push_valid,
      .push_data,
      .push_slots(slots),
      .push_slots_next(),
      .push_full(full),
      .push_full_next(),
      .pop_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .pop_rst(rst),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty(empty),
      .pop_empty_next(),
      .pop_items(items),
      .pop_items_next()
  );

  localparam int ResetActiveDelay = 1;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;
  localparam int RamReadLatency = FlopRamReadDataDepthStages;
  localparam int CutThroughLatency =
  // Push-side retiming
  br_math::max2(
      RamWriteLatency, ResetActiveDelay + 1
  ) +
  // Gray count CDC
  NumSyncStages +
  // Pop-side retiming
  1 + RamReadLatency + RegisterPopOutputs;
  localparam int BackpressureLatency = ResetActiveDelay + 1 +  // Pop-side
  NumSyncStages + 1;  // Push-side

  // Hook up the test harness
  br_fifo_test_harness #(
      .Depth(Depth),
      .Width(Width),
      .CutThroughLatency(CutThroughLatency),
      .BackpressureLatency(BackpressureLatency)
  ) br_fifo_test_harness (
      .clk,
      .rst,
      .start      (start),
      .finished   (finished),
      .error_count(error_count),
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .empty,
      .full,
      .items,
      .slots
  );

  br_test_driver #(
      .ResetCycles(10)
  ) td (
      .clk,
      .rst
  );

  // Test Sequence
  initial begin
    integer timeout;

    start = 0;

    td.reset_dut();

    $display("Starting test");

    start   = 1'b1;

    timeout = 5000;
    td.wait_cycles();
    while (timeout > 0 && !finished) td.wait_cycles();

    td.check(timeout > 0, $sformatf("Test timed out"));
    td.check(error_count == 0, $sformatf("Errors in test"));

    td.finish();
  end

endmodule
