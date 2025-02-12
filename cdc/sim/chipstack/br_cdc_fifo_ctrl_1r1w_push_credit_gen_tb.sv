// Copyright 2025 The Bedrock-RTL Authors
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

module br_cdc_fifo_ctrl_1r1w_push_credit_gen_tb;
  timeunit 1ns; timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  parameter int CLOCK_FREQ = 100;  // Clock frequency in MHz
  parameter int RESET_DURATION = 100;  // Reset duration in ns
  parameter int TIMEOUT = 10000000;  // Timeout value in ns
  parameter int PER_TASK_TIMEOUT = 1000000;  // Timeout value for each task in ns
  parameter int DRAIN_TIME = 10000;  // Time to observe all results in ns
  parameter int CLOCK_FREQ_NS_CONVERSION_FACTOR = 1000;  // Conversion factor to nanoseconds
  parameter int NO_ASSERTS_ON_RESET = 0;  // Disable assertions during reset

  //===========================================================
  // DUT Imports and Includes
  //===========================================================

  `include "br_asserts_internal.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int Depth = 5;
  parameter int Width = 4;
  parameter bit RegisterPopOutputs = 0;
  parameter int RamWriteLatency = 1;
  parameter int RamReadLatency = 0;
  parameter int NumSyncStages = 3;
  parameter int MaxCredit = Depth;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2((Depth + 1));
  localparam int CreditWidth = $clog2((MaxCredit + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic                   push_clk;
  logic                   pop_clk;
  logic                   push_rst;
  logic                   pop_rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic                   push_credit_stall;
  logic                   push_valid;
  logic [      Width-1:0] push_data;
  logic                   pop_ready;
  logic                   pop_ram_rd_data_valid;
  logic [      Width-1:0] pop_ram_rd_data;
  logic                   push_credit;
  logic                   push_full;
  logic [ CountWidth-1:0] push_slots;
  logic [CreditWidth-1:0] credit_initial_push;
  logic [CreditWidth-1:0] credit_available_push;
  logic                   push_ram_wr_valid;
  logic [  AddrWidth-1:0] push_ram_wr_addr;
  logic [      Width-1:0] push_ram_wr_data;
  logic                   pop_valid;
  logic [      Width-1:0] pop_data;
  logic                   pop_empty;
  logic [ CountWidth-1:0] pop_items;
  logic                   pop_ram_rd_addr_valid;
  logic [  AddrWidth-1:0] pop_ram_rd_addr;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  assign credit_initial_push = Depth;

  br_cdc_fifo_ctrl_1r1w_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .MaxCredit(MaxCredit)
  ) dut (
      .push_clk(push_clk),
      .pop_clk(pop_clk),
      .push_rst(push_rst),
      .pop_rst(pop_rst),
      .push_sender_in_reset(1'b0),  // unused
      .push_receiver_in_reset(),  // unused
      .push_credit_stall(1'b0),  // unused
      .push_valid(push_valid),
      .push_data(push_data),
      .credit_initial_push(credit_initial_push),
      .credit_withhold_push('0),  // unused
      .pop_ready(pop_ready),
      .pop_ram_rd_data_valid(pop_ram_rd_data_valid),
      .pop_ram_rd_data(pop_ram_rd_data),
      .push_credit(push_credit),
      .push_full(push_full),
      .push_slots(push_slots),
      .credit_count_push(),  // unused
      .credit_available_push(credit_available_push),
      .push_ram_wr_valid(push_ram_wr_valid),
      .push_ram_wr_addr(push_ram_wr_addr),
      .push_ram_wr_data(push_ram_wr_data),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .pop_empty(pop_empty),
      .pop_items(pop_items),
      .pop_ram_rd_addr_valid(pop_ram_rd_addr_valid),
      .pop_ram_rd_addr(pop_ram_rd_addr)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;

  //===========================================================
  // Clock Generation
  //===========================================================
  assign pop_clk = push_clk;
  initial begin
    push_clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) push_clk = ~push_clk;
  end
  clocking cb_push_clk @(posedge push_clk);
    default input #1step output #4;
    inout push_rst, push_credit_stall, push_valid, push_data;
    input push_credit, push_full, push_slots,
          push_ram_wr_valid, push_ram_wr_addr, push_ram_wr_data,
          credit_available_push;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout pop_rst, pop_ready, pop_ram_rd_data_valid, pop_ram_rd_data;
    input pop_valid, pop_data, pop_empty, pop_items, pop_ram_rd_addr_valid, pop_ram_rd_addr;
  endclocking


  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    if (NO_ASSERTS_ON_RESET) $assertoff;
    #(TIMEOUT);
    $display("Error: Testbench timeout!");
    $finish;
  end

  //===========================================================
  // Reset Generation
  //===========================================================
  task automatic reset_dut;
    if (NO_ASSERTS_ON_RESET) $assertoff;
    // Set all the DUT inputs to zero, making sure there are no X/Z at the inputs.
    cb_push_clk.push_valid <= 'h0;
    cb_push_clk.push_data <= 'h0;
    cb_pop_clk.pop_ready <= 'h0;
    cb_pop_clk.pop_ram_rd_data_valid <= 'h0;
    cb_pop_clk.pop_ram_rd_data <= 'h0;

    // Wiggling the reset signal.
    cb_push_clk.push_rst <= 1'bx;
    cb_pop_clk.pop_rst <= 1'bx;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    cb_push_clk.push_rst <= 1'b1;
    cb_pop_clk.pop_rst   <= 1'b1;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    cb_push_clk.push_rst <= 1'b0;
    cb_pop_clk.pop_rst   <= 1'b0;
    @(cb_push_clk);
    @(cb_pop_clk);
    #RESET_DURATION;
    if (NO_ASSERTS_ON_RESET) $asserton;
  endtask

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
    reset_dut();
    test_PushDataFlowControl();

    reset_dut();
    test_FIFOStatusFlagManagement();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end

  task automatic test_PushDataFlowControl;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_PushDataFlowControl. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // Purpose: Test the flow control for pushing data into the FIFO, ensuring data is only pushed when the FIFO is not full and the push is valid.
        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_data;
        logic [AddrWidth-1:0] expected_addr;
        logic [CountWidth-1:0] expected_slots;

        // Initial conditions
        @(cb_push_clk);
        cb_push_clk.push_rst <= 1;
        @(cb_push_clk);
        cb_push_clk.push_rst <= 0;
        @(cb_push_clk);

        // Generate random data for push_data
        random_data = $urandom();
        expected_addr = 0;
        expected_slots = Depth;

        // Apply stimulus
        cb_push_clk.push_valid <= 1;
        cb_push_clk.push_data  <= random_data;
        @(cb_push_clk);
        $display($sformatf({"Time: %0t, INFO: test_PushDataFlowControl - ",
                            "Driving push_valid=1, push_data=0x%h"}, $time, random_data));

        // Check if FIFO is not full and push operation can proceed
        if (!cb_push_clk.push_full) begin
          if (cb_push_clk.push_ram_wr_valid) begin
            $display($sformatf({"Time: %0t, INFO: test_PushDataFlowControl - ",
                                "push_ram_wr_valid asserted, write ", "operation initiated"},
                                 $time));
            if (cb_push_clk.push_ram_wr_addr != expected_addr) begin
              $display($sformatf(
                           {"Time: %0t, ERROR: test_PushDataFlowControl - Address mismatch. ",
                            "Expected 0x%h, got 0x%h"}, $time, expected_addr, push_ram_wr_addr));
              test_failed = 1;
            end else begin
              $display($sformatf(
                           {"Time: %0t, INFO: test_PushDataFlowControl - Address check passed. ",
                            "Expected and got 0x%h"}, $time, expected_addr));
            end

            if (cb_push_clk.push_ram_wr_data != random_data) begin
              $display($sformatf({"Time: %0t, ERROR: test_PushDataFlowControl - Data mismatch. ",
                                  "Expected 0x%h, got 0x%h"}, $time, random_data,
                                   push_ram_wr_data));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PushDataFlowControl - Data check passed. ",
                                  "Expected and got 0x%h"}, $time, random_data));
            end

            @(cb_push_clk);  // MANUAL FIX
            if (cb_push_clk.push_slots != expected_slots - 1) begin
              $display($sformatf({"Time: %0t, ERROR: test_PushDataFlowControl - ",
                                  "push_slots mismatch. ", "Expected %0d, got %0d"}, $time,
                                   expected_slots - 1, push_slots));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PushDataFlowControl - ",
                                  "push_slots check passed. ", "Expected and got %0d"}, $time,
                                   expected_slots - 1));
            end

            if (test_failed != 1) test_failed = 0;
          end else begin
            $display($sformatf({"Time: %0t, ERROR: test_PushDataFlowControl - ",
                                "push_ram_wr_valid not asserted ", "when expected"}, $time));
            test_failed = 1;
          end
        end else begin
          $display(
              $sformatf(
                  {"Time: %0t, INFO: test_PushDataFlowControl - FIFO is full, no push operation ",
                   "performed"}, $time));
          test_failed = 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_PushDataFlowControl", $time);
        end else begin
          $display("Time: %0t, FAILED: test_PushDataFlowControl", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask



  task automatic test_FIFOStatusFlagManagement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_FIFOStatusFlagManagement. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        // This task tests the FIFO status flag management, focusing on fullness and available slots.
        // It ensures that the status flags accurately reflect the current state of the FIFO.

        // Local variables declaration
        int test_failed = -1;
        logic [Width-1:0] random_data;

        // Ensure adequate stimulus propagation time
        @(cb_push_clk);
        @(cb_pop_clk);

        // Test sequence
        fork
          // Push operation
          begin
            repeat (Depth) begin
              random_data = $urandom();
              cb_push_clk.push_valid <= 1;
              cb_push_clk.push_data  <= random_data;
              @(cb_push_clk);
              $display($sformatf({"Time: %0t, INFO: test_FIFOStatusFlagManagement - ",
                                  "Driving push_valid=1, ", "push_data=0x%h"}, $time, random_data));
            end
            cb_push_clk.push_valid <= 0;
          end

          // Monitor and check FIFO status flags
          begin
            repeat (Depth) begin
              @(cb_push_clk);
              if (cb_push_clk.push_full && cb_push_clk.push_slots != 0) begin
                $display(
                    {"Time: %0t, ERROR: test_FIFOStatusFlagManagement - push_full asserted but ",
                     "push_slots is not zero."}, $time);
                test_failed = 1;
              end else if (!cb_push_clk.push_full && cb_push_clk.push_slots == 0) begin
                $display($sformatf({"Time: %0t, ERROR: test_FIFOStatusFlagManagement - ",
                                    "push_full not asserted but push_slots is zero."}, $time));
                test_failed = 1;
              end else begin
                $display($sformatf({"Time: %0t, INFO: test_FIFOStatusFlagManagement - ",
                                    "push_full=%b, push_slots=%d"}, $time, push_full, push_slots));
                if (test_failed != 1) test_failed = 0;
              end
            end
          end
        join

        // Final test status
        if (test_failed == 0) begin
          $display("Time: %0t, PASSED: test_FIFOStatusFlagManagement", $time);
        end else begin
          $display("Time: %0t, FAILED: test_FIFOStatusFlagManagement", $time);
          overall_tb_status = 1'b0;
        end
      end
    join_any
    disable fork;
  endtask

endmodule
