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

module br_fifo_flops_gen_tb;
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
  // DUT Parameters
  //===========================================================
  parameter int Depth = 2;
  parameter int Width = 1;
  parameter bit EnableBypass = 1;
  parameter bit RegisterPopOutputs = 0;
  parameter int FlopRamDepthTiles = 1;
  parameter int FlopRamWidthTiles = 1;
  parameter int FlopRamAddressDepthStages = 0;
  parameter int FlopRamReadDataDepthStages = 0;
  parameter int FlopRamReadDataWidthStages = 0;
  parameter bit EnableCoverPushBackpressure = 1;
  parameter bit EnableAssertPushValidStability = EnableCoverPushBackpressure;
  parameter bit EnableAssertPushDataStability = EnableAssertPushValidStability;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2((Depth + 1));

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic clk;
  logic rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic push_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic full;
  logic full_next;
  logic [CountWidth-1:0] slots;
  logic [CountWidth-1:0] slots_next;
  logic empty;
  logic empty_next;
  logic [CountWidth-1:0] items;
  logic [CountWidth-1:0] items_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RegisterPopOutputs(RegisterPopOutputs),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability)
  ) dut (
      .clk(clk),
      .rst(rst),
      .push_valid(push_valid),
      .push_data(push_data),
      .pop_ready(pop_ready),
      .push_ready(push_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .full(full),
      .full_next(full_next),
      .slots(slots),
      .slots_next(slots_next),
      .empty(empty),
      .empty_next(empty_next),
      .items(items),
      .items_next(items_next)
  );

  //===========================================================
  // Helper testbench variables
  //===========================================================
  bit overall_tb_status = 1;

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, push_valid, push_data, pop_ready;
    input push_ready, pop_valid, pop_data, full, full_next, slots,
    slots_next, empty, empty_next, items, items_next;
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
    cb_clk.push_valid <= 'h0;
    cb_clk.push_data  <= 'h0;
    cb_clk.pop_ready  <= 'h0;

    // Wiggling the reset signal.
    rst = 1'b0;
    #RESET_DURATION;
    rst = 1'b1;
    #RESET_DURATION;
    rst = 1'b0;
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
    test_BypassDataTransfer();

    reset_dut();
    test_RegisterPopOutputsControl();

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
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_PushDataFlowControl. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // Purpose: Test the push data flow control mechanism of the FIFO, ensuring data is pushed only when space is available and handling backpressure correctly.

            // Local variables declaration
            int test_failed = -1;
            logic [Width-1:0] random_push_data;
            logic [CountWidth-1:0] expected_slots_next;
            logic expected_full_next;

            // Preconditions: Ensure FIFO is reset and initialized
            @(cb_clk);
            cb_clk.rst <= 1;
            @(cb_clk);
            cb_clk.rst <= 0;
            @(cb_clk);

            // Generate random data for push_data
            random_push_data = $urandom();

            // Apply stimulus: Assert push_valid with random data
            cb_clk.push_valid <= 1;
            cb_clk.push_data  <= random_push_data;
            @(cb_clk);
            $display($sformatf({"Time: %0t, INFO: test_PushDataFlowControl- ",
                                "Driving push_valid=1, push_data=0x%h"}, $time, random_push_data));

            // Check if FIFO is not full and push_ready is asserted
            if (!cb_clk.full && cb_clk.push_ready) begin
              // Calculate expected values
              expected_slots_next = cb_clk.slots - 1;
              expected_full_next  = (expected_slots_next == 0);

              // Check slots_next and full_next
              if (cb_clk.slots_next !== expected_slots_next) begin
                $display($sformatf({"Time: %0t, ERROR: test_PushDataFlowControl- ",
                                    "Check failed. Expected slots_next=%0d, got %0d"}, $time,
                                     expected_slots_next, slots_next));
                test_failed = 1;
              end else begin
                $display(
                    $sformatf(
                        {"Time: %0t, INFO: test_PushDataFlowControl- ",
                         "Check passed. Expected slots_next=%0d is the same as the observed value."
                          }, $time, expected_slots_next));
                if (test_failed != 1) test_failed = 0;
              end

              if (cb_clk.full_next !== expected_full_next) begin
                $display($sformatf({"Time: %0t, ERROR: test_PushDataFlowControl- ",
                                    "Check failed. Expected full_next=%0b, got %0b"}, $time,
                                     expected_full_next, full_next));
                test_failed = 1;
              end else begin
                $display(
                    $sformatf(
                        {"Time: %0t, INFO: test_PushDataFlowControl- ",
                         "Check passed. Expected full_next=%0b is the same as the observed value."
                          }, $time, expected_full_next));
                if (test_failed != 1) test_failed = 0;
              end
            end else begin
              $display($sformatf(
                           {"Time: %0t, INFO: test_PushDataFlowControl- ",
                            "FIFO is full or push_ready is not asserted, skipping push operation."
                             }, $time));
            end

            // Deassert push_valid to stop pushing data
            cb_clk.push_valid <= 0;
            @(cb_clk);

            // Final test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_PushDataFlowControl", $time);
            end else begin
              $display("Time: %0t, FAILED: test_PushDataFlowControl", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  task automatic test_BypassDataTransfer;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_BypassDataTransfer. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_BypassDataTransfer. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // Purpose: Test the bypass data transfer functionality of the FIFO when EnableBypass is set.
            // Local variables declaration
            int test_failed = -1;
            logic [Width-1:0] random_push_data;
            logic [Width-1:0] observed_pop_data;
            logic expected_pop_valid;
            logic expected_push_ready;

            // Preconditions: Ensure FIFO is empty and EnableBypass is set
            @(cb_clk);
            cb_clk.rst <= 1;
            @(cb_clk);
            cb_clk.rst <= 0;
            @(cb_clk);

            // Step 1: Assert push_valid with random data and check bypass conditions
            random_push_data = $urandom();
            cb_clk.push_valid <= 1;
            cb_clk.push_data  <= random_push_data;
            cb_clk.pop_ready  <= 1;
            @(cb_clk);
            $display($sformatf({"Time: %0t, INFO: test_BypassDataTransfer- ",
                                "Driving push_valid=1, push_data=0x%h, pop_ready=1"}, $time,
                                 random_push_data));

            // Step 2: Check if FIFO is empty and EnableBypass is set
            expected_push_ready = 1;
            expected_pop_valid  = 1;
            observed_pop_data   = cb_clk.pop_data;

            if (cb_clk.push_ready !== expected_push_ready ||
            cb_clk.pop_valid !== expected_pop_valid ||
            observed_pop_data !== random_push_data) begin
              $display(
                  $sformatf(
                      {"Time: %0t, ERROR: test_BypassDataTransfer- ",
                       "Check failed. Expected push_ready=%b, pop_valid=%b, pop_data=0x%h; got push_ready=%b, pop_valid=%b, pop_data=0x%h"
                        }, $time, expected_push_ready, expected_pop_valid, random_push_data,
                        cb_clk.push_ready, cb_clk.pop_valid, observed_pop_data));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_BypassDataTransfer- ",
                                  "Check passed. Expected values match observed values."}, $time));
              if (test_failed != 1) test_failed = 0;
            end

            // Step 3: Deassert push_valid and pop_ready
            @(cb_clk);
            cb_clk.push_valid <= 0;
            cb_clk.pop_ready  <= 0;
            @(cb_clk);
            $display("Time: %0t, INFO: test_BypassDataTransfer- Driving push_valid=0, pop_ready=0",
                     $time);

            // Final check and report test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_BypassDataTransfer", $time);
            end else begin
              $display("Time: %0t, FAILED: test_BypassDataTransfer", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  task automatic test_RegisterPopOutputsControl;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_RegisterPopOutputsControl. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_RegisterPopOutputsControl. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // Purpose: Test the registration of pop outputs when RegisterPopOutputs is enabled, ensuring pop data and valid signals are registered before being output.

            // Local variables declaration
            int test_failed = -1;
            logic [Width-1:0] expected_pop_data;
            logic expected_pop_valid;
            logic [Width-1:0] random_push_data;
            logic random_pop_ready;

            // Preconditions
            @(cb_clk);
            // Ensure RegisterPopOutputs is enabled
            if (RegisterPopOutputs == 1) begin
              // Initial reset
              cb_clk.rst <= 1;
              @(cb_clk);
              cb_clk.rst <= 0;
              @(cb_clk);

              // Generate random data for push_data and pop_ready
              random_push_data = $urandom();
              random_pop_ready = $urandom_range(0, 1);

              // Apply stimulus
              cb_clk.push_valid <= 1;
              cb_clk.push_data  <= random_push_data;
              cb_clk.pop_ready  <= random_pop_ready;
              $display($sformatf({"Time: %0t, INFO: test_RegisterPopOutputsControl- ",
                                  "Driving push_valid=1, push_data=0x%h, pop_ready=%0b"}, $time,
                                   random_push_data, random_pop_ready));

              // Wait for the next clock cycle
              @(cb_clk);

              // Capture expected values
              expected_pop_data  = random_push_data;
              expected_pop_valid = 1;

              // Check if pop_valid and pop_data are registered
              if (cb_clk.pop_valid !== expected_pop_valid || cb_clk.pop_data !== expected_pop_data)
              begin
                $display(
                    $sformatf(
                        {"Time: %0t, ERROR: test_RegisterPopOutputsControl- ",
                         "Check failed. Expected pop_valid=%0b, pop_data=0x%h, got pop_valid=%0b, pop_data=0x%h"
                          }, $time, expected_pop_valid, expected_pop_data, pop_valid, pop_data));
                test_failed = 1;
              end else begin
                $display(
                    $sformatf(
                        {"Time: %0t, INFO: test_RegisterPopOutputsControl- ",
                         "Check passed. Expected pop_valid=%0b, pop_data=0x%h is the same as the observed values."
                          }, $time, expected_pop_valid, expected_pop_data));
                if (test_failed != 1) test_failed = 0;
              end

              // Disable further stimulus
              cb_clk.push_valid <= 0;
              cb_clk.pop_ready  <= 0;
              @(cb_clk);
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_RegisterPopOutputsControl- ",
                                  "RegisterPopOutputs is not enabled, skipping test."}, $time));
              test_failed = 0;
            end

            // Report test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_RegisterPopOutputsControl", $time);
            end else begin
              $display("Time: %0t, FAILED: test_RegisterPopOutputsControl", $time);
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
