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

module br_fifo_flops_push_credit_tb ();

  // 6 cycles of transport delay (2*PropDelay)
  // 2 cycles of valid->credit delay at FIFO
  // Depth of 8 allows full-throughput

  // Parameters
  localparam int Width = 8;
  localparam int Depth = 8;
  localparam int PropDelay = 3;
  localparam int NData = 100;

  // Inputs
  logic clk;
  logic rst;

  // DUT connections
  logic cv_push_credit, cv_push_credit_d;
  logic cv_push_valid, cv_push_valid_d;
  logic [Width-1:0] cv_push_data, cv_push_data_d;
  logic cv_push_credit_stall, cv_push_credit_stall_d;

  // harness push if
  logic push_ready;
  logic push_valid;
  logic [Width-1:0] push_data;

  // harness pop if
  logic pop_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;

  logic [$clog2(NData+1)-1:0] pop_count;
  logic [$clog2(Depth+1)-1:0] sender_credit, credit_initial_push;
  logic   fail;
  integer unpop;

  assign credit_initial_push = Depth;

  br_fifo_flops_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(0),
      .MaxCredit(Depth)
  ) dut (
      .clk,
      .rst,
      .push_credit_stall(cv_push_credit_stall_d),
      .push_credit(cv_push_credit),
      .push_valid(cv_push_valid_d),
      .push_data(cv_push_data_d),
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full(),
      .full_next(),
      .slots(),
      .slots_next(),
      .credit_initial_push,
      .credit_withhold_push('0),
      .credit_count_push(),
      .credit_available_push(),
      .empty(),
      .empty_next(),
      .items(),
      .items_next()
  );

  br_credit_sender #(
      .Width(Width),
      .MaxCredit(Depth)
  ) br_credit_sender (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_credit_stall(cv_push_credit_stall),
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
      .rst,
      .in({cv_push_valid, cv_push_data, cv_push_credit_stall}),
      .out({cv_push_valid_d, cv_push_data_d, cv_push_credit_stall_d}),
      .out_stages()  // ri lint_check_waive OPEN_OUTPUT
  );

  br_delay_nr #(
      .NumStages(PropDelay),
      .Width(1)
  ) br_delay_nr_from_fifo (
      .clk,
      .rst,
      .in(cv_push_credit),
      .out(cv_push_credit_d),
      .out_stages()  // ri lint_check_waive OPEN_OUTPUT
  );

  // Clock generation
  always #5 clk = ~clk;

`ifdef DUMP_WAVES
  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
`endif

  // Initialize Inputs
  initial begin
    clk = 0;
    rst = 1;
    pop_ready = 1'b1;
    push_valid = 1'b0;
    push_data = '0;
    fail = 0;

    // Wait 100 ns for global reset to finish
    #100 rst = 0;

    // wait for initial credit release
    #400;

    for (integer i = 0; i < NData; i += 1) begin
      while (!push_ready) begin
        @(posedge clk);
      end
      @(negedge clk);
      // push data
      push_valid = 1'b1;
      push_data  = i;
    end

    @(negedge clk);
    push_valid = 1'b0;
    push_data  = '0;

    #1000;

    // end of test checks
    if (pop_count != NData) begin
      $error("Test failed: pop_count=%d", pop_count);
      fail = 1;
    end
    if (sender_credit != Depth) begin
      $error("Test failed: sender_credit=%d", sender_credit);
      fail = 1;
    end
    if (unpop != 1) begin
      // check no bubbles in output - unpop should be 1
      $error("Test failed: pop_valid deasserted %d times", unpop);
      fail = 1;
    end
    // finish
    if (!fail) begin
      $display("TEST PASSED");
    end
    $finish;
  end

  initial begin
    pop_count = 0;
    while (1) begin
      @(posedge clk);
      if (pop_valid && pop_ready) begin
        pop_count = pop_count + 1;
      end
    end
  end

  initial begin
    @(negedge rst);
    unpop = 0;
    while (1) begin
      @(negedge pop_valid);
      unpop += 1;
    end
  end

endmodule
