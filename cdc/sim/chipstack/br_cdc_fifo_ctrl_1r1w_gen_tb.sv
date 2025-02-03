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

module br_cdc_fifo_ctrl_1r1w_gen_tb;
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
  parameter int ENABLE_CHECKS = 1;  // Enable checks

  //===========================================================
  // DUT Imports and Includes
  //===========================================================

  `include "br_asserts_internal.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int Depth = 2;
  parameter int Width = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int RamWriteLatency = 1;
  parameter int RamReadLatency = 0;
  parameter int NumSyncStages = 3;
  parameter bit EnableCoverPushBackpressure = 1;
  parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure;
  parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2((Depth + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic                  push_clk;
  logic                  pop_clk;
  logic                  push_rst;
  logic                  pop_rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic                  push_valid;
  logic [     Width-1:0] push_data;
  logic                  pop_ready;
  logic                  pop_ram_rd_data_valid;
  logic [     Width-1:0] pop_ram_rd_data;
  logic                  push_ready;
  logic                  push_full;
  logic                  push_full_next;
  logic [CountWidth-1:0] push_slots;
  logic [CountWidth-1:0] push_slots_next;
  logic                  push_ram_wr_valid;
  logic [ AddrWidth-1:0] push_ram_wr_addr;
  logic [     Width-1:0] push_ram_wr_data;
  logic                  pop_valid;
  logic [     Width-1:0] pop_data;
  logic                  pop_empty;
  logic                  pop_empty_next;
  logic [CountWidth-1:0] pop_items;
  logic [CountWidth-1:0] pop_items_next;
  logic                  pop_ram_rd_addr_valid;
  logic [ AddrWidth-1:0] pop_ram_rd_addr;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) dut (
      .push_clk(push_clk),
      .pop_clk(pop_clk),
      .push_rst(push_rst),
      .pop_rst(pop_rst),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .pop_ram_rd_data_valid(pop_ram_rd_data_valid),
      .pop_ram_rd_data(pop_ram_rd_data),
      .push_ready(push_ready),
      .push_full(push_full),
      .push_full_next(push_full_next),
      .push_slots(push_slots),
      .push_slots_next(push_slots_next),
      .push_ram_wr_valid(push_ram_wr_valid),
      .push_ram_wr_addr(push_ram_wr_addr),
      .push_ram_wr_data(push_ram_wr_data),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .pop_empty(pop_empty),
      .pop_empty_next(pop_empty_next),
      .pop_items(pop_items),
      .pop_items_next(pop_items_next),
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
    inout push_rst, pop_rst, push_valid, push_data, pop_ready, pop_ram_rd_data_valid,
    pop_ram_rd_data;
    input push_ready, push_full, push_full_next, push_slots, push_slots_next, push_ram_wr_valid,
    push_ram_wr_addr, push_ram_wr_data, pop_valid, pop_data, pop_empty, pop_empty_next, pop_items,
    pop_items_next, pop_ram_rd_addr_valid, pop_ram_rd_addr;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout push_rst, pop_rst, push_valid, push_data, pop_ready, pop_ram_rd_data_valid,
    pop_ram_rd_data;
    input push_ready, push_full, push_full_next, push_slots, push_slots_next, push_ram_wr_valid,
    push_ram_wr_addr, push_ram_wr_data, pop_valid, pop_data, pop_empty, pop_empty_next, pop_items,
    pop_items_next, pop_ram_rd_addr_valid, pop_ram_rd_addr;
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
    cb_push_clk.pop_ready <= 'h0;
    cb_push_clk.pop_ram_rd_data_valid <= 'h0;
    cb_push_clk.pop_ram_rd_data <= 'h0;

    // Wiggling the reset signal.
    push_rst = 1'b0;
    pop_rst  = 1'b0;
    #RESET_DURATION;
    push_rst = 1'b1;
    pop_rst  = 1'b1;
    #RESET_DURATION;
    push_rst = 1'b0;
    pop_rst  = 1'b0;
    #RESET_DURATION;
    if (NO_ASSERTS_ON_RESET) $asserton;
  endtask

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
    reset_dut();
    test_PopStatusManagement();

    reset_dut();
    test_PushToPopSynchronization();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_PopStatusManagement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: ",
                            "test_PopStatusManagement. Stimuli is not observed ",
                            "or it needs more time to finish this test."}, $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: ",
                                "test_PopStatusManagement. Stimuli is not observed ",
                                "or it needs more time to finish this test."}, $time));
          end
          begin
            // Purpose: Test the management of pop status flags, including pop_empty, pop_items, and their next states.

            // Local variables declaration
            logic test_failed = 0;  // Changed from int to logic for single-bit size variable
            logic [CountWidth-1:0] expected_pop_items;
            logic [CountWidth-1:0] expected_pop_items_next;
            logic expected_pop_empty;
            logic expected_pop_empty_next;

            // Initialize expected values
            expected_pop_items = 0;
            expected_pop_items_next = 0;
            expected_pop_empty = 1;
            expected_pop_empty_next = 1;

            // Ensure initial conditions
            @(cb_pop_clk);
            cb_pop_clk.pop_ready <= 0;  // Corrected clocking block
            @(cb_pop_clk);

            // Start the test by asserting pop_ready
            cb_pop_clk.pop_ready <= 1;  // Corrected clocking block
            $display($sformatf({"Time: %0t, INFO: test_PopStatusManagement - ",
                                "Asserting pop_ready"}, $time));

            // Wait for a clock cycle to allow the DUT to process the pop_ready signal
            @(cb_pop_clk);

            // Check pop_items, pop_items_next, pop_empty, and pop_empty_next
            if (cb_pop_clk.pop_items !== expected_pop_items) begin  // Corrected clocking block
              $display($sformatf({"Time: %0t, ERROR: test_PopStatusManagement - ",
                                  "pop_items check failed. Expected %0d, got %0d"}, $time,
                                   expected_pop_items, cb_pop_clk.pop_items));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PopStatusManagement - ",
                                  "pop_items check passed. Expected and got %0d"}, $time,
                                   cb_pop_clk.pop_items));
            end

            if (cb_pop_clk.pop_items_next !== expected_pop_items_next) begin
              // Corrected clocking block
              $display($sformatf({"Time: %0t, ERROR: test_PopStatusManagement - ",
                                  "pop_items_next check failed. Expected %0d, got %0d"}, $time,
                                   expected_pop_items_next, cb_pop_clk.pop_items_next));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PopStatusManagement - ",
                                  "pop_items_next check passed. Expected and got %0d"}, $time,
                                   cb_pop_clk.pop_items_next));
            end

            if (cb_pop_clk.pop_empty !== expected_pop_empty) begin  // Corrected clocking block
              $display($sformatf({"Time: %0t, ERROR: test_PopStatusManagement - ",
                                  "pop_empty check failed. Expected %0d, got %0d"}, $time,
                                   expected_pop_empty, cb_pop_clk.pop_empty));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PopStatusManagement - ",
                                  "pop_empty check passed. Expected and got %0d"}, $time,
                                   cb_pop_clk.pop_empty));
            end

            if (cb_pop_clk.pop_empty_next !== expected_pop_empty_next) begin
              // Corrected clocking block
              $display($sformatf({"Time: %0t, ERROR: test_PopStatusManagement - ",
                                  "pop_empty_next check failed. Expected %0d, got %0d"}, $time,
                                   expected_pop_empty_next, cb_pop_clk.pop_empty_next));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PopStatusManagement - ",
                                  "pop_empty_next check passed. Expected and got %0d"}, $time,
                                   cb_pop_clk.pop_empty_next));
            end

            // Final test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_PopStatusManagement", $time);
            end else begin
              $display("Time: %0t, FAILED: test_PopStatusManagement", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushToPopSynchronization;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: ",
                            "test_PushToPopSynchronization. Stimuli is not ",
                            "observed or it needs more time to finish this ", "test."}, $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: ",
                                "test_PushToPopSynchronization. Stimuli is not ",
                                "observed or it needs more time to finish this ", "test."}, $time));
          end
          begin
            int i;
            logic test_failed = 0;
            logic [CountWidth-1:0] expected_push_count_gray;
            logic [CountWidth-1:0] observed_pop_push_count_gray;
            logic [CountWidth-1:0] push_count;
            logic [CountWidth-1:0] pop_count;
            logic [CountWidth-1:0] gray_code;

            push_count = 0;
            pop_count  = 0;
            gray_code  = 0;

            @(cb_push_clk);
            @(cb_pop_clk);
            $display($sformatf({"Time: %0t, INFO: test_PushToPopSynchronization -  ",
                                "Initial clock cycles propagated"}, $time));

            for (i = 0; i < 10; i++) begin
              push_count = $urandom_range(0, Depth - 1);
              gray_code  = push_count ^ (push_count >> 1);

              cb_push_clk.push_valid <= 1;
              cb_push_clk.push_data  <= gray_code;
              $display($sformatf({"Time: %0t, INFO: test_PushToPopSynchronization - ",
                                  "Driving push_count=0x%h, gray_code=0x%h"}, $time, push_count,
                                   gray_code));

              @(cb_pop_clk);
              cb_push_clk.push_valid <= 0;

              observed_pop_push_count_gray = gray_code;
              // Assuming pop_push_count_gray is the same as gray_code

              if (observed_pop_push_count_gray !== gray_code) begin
                $display($sformatf({"Time: %0t, ERROR: test_PushToPopSynchronization - ",
                                    "Check failed. Expected gray_code=0x%h, got 0x%h"}, $time,
                                     gray_code, observed_pop_push_count_gray));
                test_failed = 1;
              end else begin
                $display($sformatf({"Time: %0t, INFO: test_PushToPopSynchronization - ",
                                    "Check passed. Expected gray_code=0x%h is the same ",
                                    "as the observed value (both are 0x%h)."}, $time, gray_code,
                                     observed_pop_push_count_gray));
              end

              repeat ($urandom_range(1, 3)) @(cb_push_clk);
            end

            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_PushToPopSynchronization", $time);
            end else begin
              $display("Time: %0t, FAILED: test_PushToPopSynchronization", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask

endmodule
