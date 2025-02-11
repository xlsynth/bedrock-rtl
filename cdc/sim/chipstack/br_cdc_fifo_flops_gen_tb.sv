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


module br_cdc_fifo_flops_gen_tb;
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
  parameter bit RegisterPopOutputs = 0;
  parameter int NumSyncStages = 3;
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
  logic push_clk;
  logic pop_clk;
  logic push_rst;
  logic pop_rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic push_valid;
  logic [Width-1:0] push_data;
  logic pop_ready;
  logic push_ready;
  logic pop_valid;
  logic [Width-1:0] pop_data;
  logic push_full;
  logic push_full_next;
  logic [CountWidth-1:0] push_slots;
  logic [CountWidth-1:0] push_slots_next;
  logic pop_empty;
  logic pop_empty_next;
  logic [CountWidth-1:0] pop_items;
  logic [CountWidth-1:0] pop_items_next;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_flops #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .NumSyncStages(NumSyncStages),
      .FlopRamDepthTiles(FlopRamDepthTiles),
      .FlopRamWidthTiles(FlopRamWidthTiles),
      .FlopRamAddressDepthStages(FlopRamAddressDepthStages),
      .FlopRamReadDataDepthStages(FlopRamReadDataDepthStages),
      .FlopRamReadDataWidthStages(FlopRamReadDataWidthStages),
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
      .push_ready(push_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .push_full(push_full),
      .push_full_next(push_full_next),
      .push_slots(push_slots),
      .push_slots_next(push_slots_next),
      .pop_empty(pop_empty),
      .pop_empty_next(pop_empty_next),
      .pop_items(pop_items),
      .pop_items_next(pop_items_next)
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
    inout push_rst, push_valid, push_data;
    input push_ready, push_full, push_full_next, push_slots, push_slots_next;
  endclocking

  clocking cb_pop_clk @(posedge pop_clk);
    default input #1step output #4;
    inout pop_rst, pop_ready;
    input pop_valid, pop_data, pop_empty, pop_empty_next, pop_items, pop_items_next;
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
    cb_push_clk.push_data  <= 'h0;
    cb_pop_clk.pop_ready   <= 'h0;

    // Wiggling the reset signal.
    push_rst = 1'bx;
    pop_rst  = 1'bx;
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
    test_StabilityOfPushValidSignal();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_StabilityOfPushValidSignal;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: ",
                            "test_StabilityOfPushValidSignal. Stimuli is not ",
                            "observed or it needs more time to finish this ", "test."}, $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: ",
                                "test_StabilityOfPushValidSignal. Stimuli is not ",
                                "observed or it needs more time to finish this ", "test."}, $time));
          end
          begin
            // This task verifies the stability of the `push_valid` signal during backpressure conditions.
            // It ensures that `push_valid` remains stable when the FIFO is unable to accept new data.

            // Local variables declaration
            logic test_failed = 1'b0;
            logic [Width-1:0] push_data_value;
            logic push_valid_value;
            int i;

            // Initial setup
            cb_push_clk.push_valid <= 1'b0;
            cb_push_clk.push_data  <= '0;
            @(cb_push_clk);

            // Generate random data and set push_valid
            push_data_value  = $urandom();
            push_valid_value = 1'b1;
            cb_push_clk.push_data  <= push_data_value;
            cb_push_clk.push_valid <= push_valid_value;
            $display($sformatf({"Time: %0t, INFO: test_StabilityOfPushValidSignal -",
                                " Driving push_valid=1, push_data=0x%h"}, $time, push_data_value));

            // Monitor push_full and check push_valid stability
            for (i = 0; i < 10; i++) begin
              @(cb_push_clk);

              if (cb_push_clk.push_full) begin
                // Check if push_valid remains stable
                if (cb_push_clk.push_valid !== push_valid_value) begin
                  $display($sformatf({"Time: %0t, ERROR: test_StabilityOfPushValidSignal ",
                                      "- push_valid changed during backpressure. Expected",
                                      " %b, got %b"}, $time, push_valid_value,
                                       cb_push_clk.push_valid));
                  test_failed = 1'b1;
                end else begin
                  $display($sformatf({"Time: %0t, INFO: test_StabilityOfPushValidSignal -",
                                      " push_valid is stable during backpressure."}, $time));
                end
              end

              // If push_ready is asserted, stop driving push_valid
              if (cb_push_clk.push_ready) begin
                cb_push_clk.push_valid <= 1'b0;
                $display($sformatf({"Time: %0t, INFO: test_StabilityOfPushValidSignal -",
                                    " push_ready asserted, stopping push_valid"}, $time));
                break;
              end
            end

            // Final test status
            if (!test_failed) begin
              $display($sformatf({"Time: %0t, PASSED: test_StabilityOfPushValidSignal"}, $time));
            end else begin
              $display($sformatf({"Time: %0t, FAILED: test_StabilityOfPushValidSignal"}, $time));
              overall_tb_status = 1'b0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask

  asrt_push_valid_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(push_valid)))
  else $error("push_valid is X after reset!");

  asrt_push_data_not_unknown :
  assert property (@(posedge push_clk) disable iff (push_rst !== 1'b0) (!$isunknown(push_data)))
  else $error("push_data is X after reset!");

  asrt_pop_ready_not_unknown :
  assert property (@(posedge pop_clk) disable iff (pop_rst !== 1'b0) (!$isunknown(pop_ready)))
  else $error("pop_ready is X after reset!");

endmodule
