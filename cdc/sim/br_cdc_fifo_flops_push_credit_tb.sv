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

`timescale 1ns / 1ps

module br_cdc_fifo_flops_push_credit_tb ();

  // Parameters
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterPushOutputs = 0;
  parameter int FlopRamAddressDepthStages = 0;
  parameter int FlopRamReadDataDepthStages = 0;
  parameter int NumSyncStages = 2;

  localparam int PropDelay = 3;
  localparam int Width = 8;
  localparam int RamWriteLatency = FlopRamAddressDepthStages + 1;
  localparam int RamReadLatency = FlopRamAddressDepthStages + FlopRamReadDataDepthStages;
  localparam int CutThroughLatency = PropDelay + br_math::max2(
      2, RamWriteLatency + 1
  ) +  // push-side latency
  NumSyncStages + 1 + RamReadLatency + RegisterPopOutputs;  // pop-side latency
  localparam int BackpressureLatency = 2 + NumSyncStages + 1 + RegisterPushOutputs + PropDelay;
  localparam int Depth = CutThroughLatency + BackpressureLatency + 1;
  localparam int NData = 100;

  // Inputs
  // Clock and reset
  // TODO(zhemao): Set up test with different push and pop clocks
  logic clk;
  logic rst;

  // DUT connections
  logic cv_push_credit, cv_push_credit_d;
  logic cv_push_valid, cv_push_valid_d;
  logic [Width-1:0] cv_push_data, cv_push_data_d;
  logic cv_push_sender_in_reset, cv_push_sender_in_reset_d;
  logic cv_push_receiver_in_reset, cv_push_receiver_in_reset_d;

  // harness push if
  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;

  // harness pop if
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic empty, full;
  logic [$clog2(Depth+1)-1:0] items, slots;

  logic [$clog2(Depth+1)-1:0] sender_credit, credit_initial_push;

  assign credit_initial_push = Depth;

  logic start;
  logic finished;
  logic [31:0] error_count;

  br_cdc_fifo_flops_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .NumSyncStages(NumSyncStages),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterPushOutputs(RegisterPushOutputs),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .MaxCredit(Depth)
  ) dut (
      .push_clk(clk),
      .push_rst(rst),
      .push_sender_in_reset(cv_push_sender_in_reset_d),
      .push_receiver_in_reset(cv_push_receiver_in_reset),
      .push_credit_stall(1'b0),
      .push_credit(cv_push_credit),
      .push_valid(cv_push_valid_d),
      .push_data(cv_push_data_d),
      .push_full(full),
      .push_slots(slots),
      .credit_initial_push,
      .credit_withhold_push('0),
      .credit_count_push(),
      .credit_available_push(),
      .pop_clk(clk),
      .pop_rst(rst),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .pop_empty(empty),
      .pop_items(items)
  );

  br_credit_sender #(
      .Width(Width),
      .MaxCredit(Depth),
      // The test harness causes instability on the push_valid,
      // so need to disable the stability check
      .EnableAssertPushValidStability(0)
  ) br_credit_sender (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset(cv_push_sender_in_reset),
      .pop_receiver_in_reset(cv_push_receiver_in_reset_d),
      .pop_credit(cv_push_credit_d),
      .pop_valid(cv_push_valid),
      .pop_data(cv_push_data),
      .credit_initial('0),
      .credit_withhold('0),
      .credit_count(sender_credit),
      .credit_available()
  );

  br_delay_nr #(
      .NumStages(PropDelay),
      .Width(Width + 2)
  ) br_delay_nr_to_fifo (
      .clk,
      .in({cv_push_valid, cv_push_data, cv_push_sender_in_reset}),
      .out({cv_push_valid_d, cv_push_data_d, cv_push_sender_in_reset_d}),
      .out_stages()
  );

  br_delay_nr #(
      .NumStages(PropDelay),
      .Width(2)
  ) br_delay_nr_from_fifo (
      .clk,
      .in({cv_push_credit, cv_push_receiver_in_reset}),
      .out({cv_push_credit_d, cv_push_receiver_in_reset_d}),
      .out_stages()
  );

  br_test_driver #(
      // Need to wait twice the prop delay for Xs to clear out
      .ResetCycles(2 * PropDelay + 1)
  ) td (
      .clk,
      .rst
  );

  br_fifo_test_harness #(
      .Width(Width),
      .Depth(Depth),
      .CutThroughLatency(CutThroughLatency),
      .BackpressureLatency(BackpressureLatency)
  ) br_fifo_test_harness (
      .clk,
      .rst,
      .start,
      .finished,
      .error_count,
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

  // Test Sequence
  initial begin
    integer timeout;

    start = 0;

    $display("Resetting DUT");

    td.reset_dut();

    $display("Waiting for initial credit return");
    while (sender_credit != credit_initial_push) begin
      td.wait_cycles();
    end

    $display("Starting test");

    start   = 1'b1;

    timeout = 5000;
    td.wait_cycles();
    while (timeout > 0 && !finished) begin
      td.wait_cycles();
      timeout = timeout - 1;
    end

    td.check(timeout > 0, $sformatf("Test timed out"));
    td.check(error_count == 0, $sformatf("Errors in test"));

    td.finish();
  end
endmodule
