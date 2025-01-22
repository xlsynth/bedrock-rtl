//=============================================================
// Testbench for Module: br_cdc_fifo_ctrl_1r1w
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_cdc_fifo_ctrl_1r1w
//=============================================================

module tb;
  timeunit 1ns;
  timeprecision 100ps;

  //===========================================================
  // Testbench Parameters
  //===========================================================
  parameter CLOCK_FREQ = 100;     // Clock frequency in MHz
  parameter RESET_DURATION = 100;    // Reset duration in ns
  parameter TIMEOUT = 10000000;          // Timeout value in ns
  parameter PER_TASK_TIMEOUT = 1000000; // Timeout value for each task in ns
  parameter DRAIN_TIME = 10000;        // Time to observe all results in ns
  parameter CLOCK_FREQ_NS_CONVERSION_FACTOR = 1000; // Conversion factor to nanoseconds
  parameter NO_ASSERTS_ON_RESET = 0;  // Disable assertions during reset
  parameter DISABLE_CHECKS = 0;  // Disable checks
  
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
  logic push_clk;
  logic pop_clk;
  logic push_rst;
  logic pop_rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic push_valid;
  logic[Width-1:0] push_data;
  logic pop_ready;
  logic pop_ram_rd_data_valid;
  logic[    Width-1:0] pop_ram_rd_data;
  logic push_ready;
  logic push_full;
  logic push_full_next;
  logic[CountWidth-1:0] push_slots;
  logic[CountWidth-1:0] push_slots_next;
  logic push_ram_wr_valid;
  logic[AddrWidth-1:0] push_ram_wr_addr;
  logic[    Width-1:0] push_ram_wr_data;
  logic pop_valid;
  logic[Width-1:0] pop_data;
  logic pop_empty;
  logic pop_empty_next;
  logic[CountWidth-1:0] pop_items;
  logic[CountWidth-1:0] pop_items_next;
  logic pop_ram_rd_addr_valid;
  logic[AddrWidth-1:0] pop_ram_rd_addr;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_cdc_fifo_ctrl_1r1w 
      #(
          .Depth(Depth),
          .Width(Width),
          .RegisterPopOutputs(RegisterPopOutputs),
          .RamWriteLatency(RamWriteLatency),
          .RamReadLatency(RamReadLatency),
          .NumSyncStages(NumSyncStages),
          .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
          .EnableAssertPushValidStability(EnableAssertPushValidStability),
          .EnableAssertPushDataStability(EnableAssertPushDataStability)
      )  dut (
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
  int test_failed = -1;
  
  //===========================================================
  // Clock Generation
  //===========================================================
  assign pop_clk = push_clk;
  initial begin
      push_clk = 1'b0;
      forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR/(2*CLOCK_FREQ)) push_clk = ~push_clk;
  end
  clocking cb_push_clk @(posedge push_clk);
      default input #1step output #4;
      inout push_rst, pop_rst, push_valid, push_data, pop_ready, pop_ram_rd_data_valid, pop_ram_rd_data;
      input push_ready, push_full, push_full_next, push_slots, push_slots_next, push_ram_wr_valid, push_ram_wr_addr, push_ram_wr_data, pop_valid, pop_data, pop_empty, pop_empty_next, pop_items, pop_items_next, pop_ram_rd_addr_valid, pop_ram_rd_addr;
  endclocking
  
  clocking cb_pop_clk @(posedge pop_clk);
      default input #1step output #4;
      inout push_rst, pop_rst, push_valid, push_data, pop_ready, pop_ram_rd_data_valid, pop_ram_rd_data;
      input push_ready, push_full, push_full_next, push_slots, push_slots_next, push_ram_wr_valid, push_ram_wr_addr, push_ram_wr_data, pop_valid, pop_data, pop_empty, pop_empty_next, pop_items, pop_items_next, pop_ram_rd_addr_valid, pop_ram_rd_addr;
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
      pop_rst = 1'b0;
      #RESET_DURATION;
      push_rst = 1'b1;
      pop_rst = 1'b1;
      #RESET_DURATION;
      push_rst = 1'b0;
      pop_rst = 1'b0;
      #RESET_DURATION;
      if (NO_ASSERTS_ON_RESET) $asserton;
  endtask

  //===========================================================
  // Initial Block to Call Tasks
  //===========================================================
  initial begin
      reset_dut();
      test_PushDataHandling();
  
      reset_dut();
      test_PushBackpressureManagement();
  
      reset_dut();
      test_PopDataRetrieval();
  
      reset_dut();
      test_GrayEncodedCounterSynchronizationPushToPop();
  
    $finish;
  end

  
  task automatic test_PushDataHandling;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display("Time: %0t, INFO: Timeout: test_PushDataHandling. Stimuli is not observed or it needs more time to finish this test.", $time);
      end
      begin
          // This task tests the Push Data Handling functionality of the FIFO, ensuring data is pushed correctly when the FIFO is not full.
          
          // Local variables declaration
          int test_failed = -1;
          logic [Width-1:0] random_data;
          logic [AddrWidth-1:0] expected_addr;
          logic [CountWidth-1:0] expected_slots_next;
          logic expected_full_next;
          
          // Initial conditions
          @(cb_push_clk);
          cb_push_clk.push_valid <= 0;
          cb_push_clk.push_data <= 0;
          expected_addr = 0;
          expected_slots_next = Depth;
          expected_full_next = 0;
          
          // Generate random data and apply stimulus
          fork
            begin
              repeat (Depth) begin
                @(cb_push_clk);
                random_data = $urandom();
                cb_push_clk.push_valid <= 1;
                cb_push_clk.push_data <= random_data;
                $display("Time: %0t, INFO: test_PushDataHandling - Driving push_valid=1, push_data=0x%h", $time, random_data);

                @(cb_push_clk);
                if (cb_push_clk.push_ready) begin
                  expected_slots_next = expected_slots_next - 1;
                  // Check push_ram_wr_valid, push_ram_wr_addr, push_ram_wr_data
                  if (cb_push_clk.push_ram_wr_valid !== 1 || cb_push_clk.push_ram_wr_addr !== expected_addr || cb_push_clk.push_ram_wr_data !== random_data) begin
                    $display("Time: %0t, ERROR: test_PushDataHandling - Check failed. Expected push_ram_wr_valid=1, push_ram_wr_addr=0x%h, push_ram_wr_data=0x%h, got push_ram_wr_valid=%b, push_ram_wr_addr=0x%h, push_ram_wr_data=0x%h", 
                             $time, expected_addr, random_data, cb_push_clk.push_ram_wr_valid, cb_push_clk.push_ram_wr_addr, cb_push_clk.push_ram_wr_data);
                    test_failed = 1;
                  end else begin
                    $display("Time: %0t, INFO: test_PushDataHandling - Check passed. Expected values for push_ram_wr_valid, push_ram_wr_addr, push_ram_wr_data are correct.", $time);
                    if (test_failed != 1)
                      test_failed = 0;
                    expected_addr = expected_addr + 1;
                  end

                  // Check push_slots_next, push_full_next
                  if (cb_push_clk.push_slots_next !== expected_slots_next || cb_push_clk.push_full_next !== expected_full_next) begin
                    $display("Time: %0t, ERROR: test_PushDataHandling - Check failed. Expected push_slots_next=0x%h, push_full_next=%b, got push_slots_next=0x%h, push_full_next=%b", 
                             $time, expected_slots_next, expected_full_next, cb_push_clk.push_slots_next, cb_push_clk.push_full_next);
                    test_failed = 1;
                  end else begin
                    $display("Time: %0t, INFO: test_PushDataHandling - Check passed. Expected values for push_slots_next and push_full_next are correct.", $time);
                    if (test_failed != 1)
                      test_failed = 0;
                    expected_full_next = (expected_slots_next == 1);
                  end
                end
              end
            end
          join
          
          // Final test status
          if (test_failed == 0) begin
            $display("Time: %0t, PASSED: test_PushDataHandling", $time);
          end else begin
            $display("Time: %0t, FAILED: test_PushDataHandling", $time);
          end
      end
    join_any
    disable fork;
  endtask
  
  
  task automatic test_PushBackpressureManagement;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display("Time: %0t, INFO: Timeout: test_PushBackpressureManagement. Stimuli is not observed or it needs more time to finish this test.", $time);
      end
      begin
          // This task tests the push backpressure management of the FIFO by asserting `push_valid` and checking if `push_ready` is deasserted when `push_full` is asserted.
          
          // Local variables declaration
          int test_failed = -1;
          logic [Width-1:0] random_push_data;
          int i;
          
          // Initial setup
          @(cb_push_clk);
          cb_push_clk.push_valid <= 0;
          cb_push_clk.push_data <= 0;
          @(cb_pop_clk);
          
          // Begin test
          for (i = 0; i < Depth + 2; i++) begin
            // Generate random data for push_data
            random_push_data = $urandom();
            
            // Apply stimulus
            cb_push_clk.push_valid <= 1;
            cb_push_clk.push_data <= random_push_data;
            $display("Time: %0t, INFO: test_PushBackpressureManagement - Driving push_valid=1, push_data=0x%h", $time, random_push_data);
          
            // Wait for one clock cycle
            @(cb_push_clk);
          
            // Check if push_full is asserted and push_ready is deasserted
            if (cb_push_clk.push_full && !cb_push_clk.push_ready) begin
              $display("Time: %0t, INFO: test_PushBackpressureManagement - Backpressure applied correctly. push_full=1, push_ready=0", $time);
              if (test_failed != 1)
                test_failed = 0;
            end else if (cb_push_clk.push_full && cb_push_clk.push_ready) begin
              $display("Time: %0t, ERROR: test_PushBackpressureManagement - Backpressure not applied. Expected push_ready=0, got push_ready=1", $time);
              test_failed = 1;
            end
          
            // Random delay to simulate real-world conditions
            repeat($urandom_range(1, 3)) @(cb_push_clk);
          end
          
          // Disable further stimulus
          cb_push_clk.push_valid <= 0;
          cb_push_clk.push_data <= 0;
          @(cb_push_clk);
          
          // Final check and report
          if (test_failed == 0) begin
            $display("Time: %0t, PASSED: test_PushBackpressureManagement", $time);
          end else begin
            $display("Time: %0t, FAILED: test_PushBackpressureManagement", $time);
          end
      end
    join_any
    disable fork;
  endtask
  
  
  task automatic test_PopDataRetrieval;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display("Time: %0t, INFO: Timeout: test_PopDataRetrieval. Stimuli is not observed or it needs more time to finish this test.", $time);
      end
      begin
          // This task tests the Pop Data Retrieval functionality of the FIFO.
          // It ensures that data is correctly output when the FIFO is not empty and the pop request is valid.
          
          // Local variables declaration
          int test_failed = -1;
          logic [Width-1:0] expected_pop_data;
          logic [AddrWidth-1:0] expected_pop_ram_rd_addr;
          logic [CountWidth-1:0] expected_pop_items;
          logic [CountWidth-1:0] expected_pop_items_next;
          logic expected_pop_empty_next;
          int random_data;
          
          // Initial setup
          @(cb_pop_clk);
          cb_pop_clk.pop_ready <= 1'b0;
          expected_pop_data = '0;
          expected_pop_ram_rd_addr = '0;
          expected_pop_items = '0;
          expected_pop_items_next = '0;
          expected_pop_empty_next = 1'b1;

          // First put some data into FIFO
          @(cb_push_clk);
          random_data = $urandom();
          cb_push_clk.push_valid <= 1;
          cb_push_clk.push_data <= random_data;
          $display("Time: %0t, INFO: test_PushDataHandling - Driving push_valid=1, push_data=0x%h", $time, random_data);
          @(cb_push_clk);
          cb_push_clk.push_valid <= 1;
          @(cb_push_clk);
          
          // Wait for the FIFO to have data
          while (cb_push_clk.pop_empty) begin
            @(cb_pop_clk);
          end
          
          // Wait for pop_valid to be asserted
          while (!cb_push_clk.pop_valid) begin
            @(cb_pop_clk);
          end
          $display("Time: %0t, INFO: test_PopDataRetrieval - pop_valid seen", $time);

          expected_pop_data = $urandom();
          // Start the pop operation
          @(cb_pop_clk);
          cb_pop_clk.pop_ready <= 1'b1;
          cb_pop_clk.pop_ram_rd_data_valid <= 1'b1;
          cb_pop_clk.pop_ram_rd_data <= expected_pop_data;
          $display("Time: %0t, INFO: test_PopDataRetrieval - pop_ready asserted", $time);
          @(cb_pop_clk);
          // Check pop_data
          if (cb_push_clk.pop_data !== expected_pop_data) begin
            $display("Time: %0t, ERROR: test_PopDataRetrieval - pop_data mismatch. Expected: 0x%h, Got: 0x%h", $time, expected_pop_data, pop_data);
            test_failed = 1;
          end else begin
            $display("Time: %0t, INFO: test_PopDataRetrieval - pop_data check passed. Value: 0x%h", $time, pop_data);
            if (test_failed != 1)
              test_failed = 0;
          end

          // Check pop_ram_rd_addr_valid
          if (!cb_push_clk.pop_ram_rd_addr_valid) begin
            $display("Time: %0t, ERROR: test_PopDataRetrieval - pop_ram_rd_addr_valid not asserted", $time);
            test_failed = 1;
          end else begin
            $display("Time: %0t, INFO: test_PopDataRetrieval - pop_ram_rd_addr_valid asserted", $time);
            if (test_failed != 1)
              test_failed = 0;
          end

          // Capture expected values
          expected_pop_items = cb_push_clk.pop_items - 1;
          expected_pop_items_next = cb_push_clk.pop_items_next - 1;
          expected_pop_empty_next = (expected_pop_items_next == 0);
          @(cb_pop_clk);

          // Check pop_items and pop_items_next
          if (cb_push_clk.pop_items !== expected_pop_items) begin
            $display("Time: %0t, ERROR: test_PopDataRetrieval - pop_items mismatch. Expected: %0d, Got: %0d", $time, expected_pop_items, cb_push_clk.pop_items);
            test_failed = 1;
          end else begin
            $display("Time: %0t, INFO: test_PopDataRetrieval - pop_items check passed. Value: %0d", $time, cb_push_clk.pop_items);
            if (test_failed != 1)
              test_failed = 0;
          end
          
          if (cb_push_clk.pop_items_next !== expected_pop_items_next) begin
            $display("Time: %0t, ERROR: test_PopDataRetrieval - pop_items_next mismatch. Expected: %0d, Got: %0d", $time, expected_pop_items_next, cb_push_clk.pop_items_next);
            test_failed = 1;
          end else begin
            $display("Time: %0t, INFO: test_PopDataRetrieval - pop_items_next check passed. Value: %0d", $time, cb_push_clk.pop_items_next);
            if (test_failed != 1)
              test_failed = 0;
          end
          
          // Check pop_empty_next
          if (cb_push_clk.pop_empty_next !== expected_pop_empty_next) begin
            $display("Time: %0t, ERROR: test_PopDataRetrieval - pop_empty_next mismatch. Expected: %b, Got: %b", $time, expected_pop_empty_next, cb_push_clk.pop_empty_next);
            test_failed = 1;
          end else begin
            $display("Time: %0t, INFO: test_PopDataRetrieval - pop_empty_next check passed. Value: %b", $time, pop_empty_next);
            if (test_failed != 1)
              test_failed = 0;
          end
          @(cb_pop_clk);
          
          // Final test status
          if (test_failed == 0) begin
            $display("Time: %0t, PASSED: test_PopDataRetrieval", $time);
          end else begin
            $display("Time: %0t, FAILED: test_PopDataRetrieval", $time);
          end
      end
    join_any
    disable fork;
  endtask
  
  
  task automatic test_GrayEncodedCounterSynchronizationPushToPop;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display("Time: %0t, INFO: Timeout: test_GrayEncodedCounterSynchronizationPushToPop. Stimuli is not observed or it needs more time to finish this test.", $time);
      end
      begin
          int test_failed = -1;
          logic [CountWidth-1:0] expected_push_count_gray;
          logic [CountWidth-1:0] observed_pop_count_gray;
          int i;
          
          expected_push_count_gray = 0;
          observed_pop_count_gray = 0;
          
          @(cb_push_clk);
          @(cb_pop_clk);
          
          for (i = 0; i < 10; i++) begin
              expected_push_count_gray = $urandom_range(0, Depth);
              cb_push_clk.push_valid <= expected_push_count_gray;
              $display("Time: %0t, INFO: test_GrayEncodedCounterSynchronizationPushToPop - Driving push_push_count_gray=0x%h", $time, expected_push_count_gray);
          
              repeat (NumSyncStages + 1) @(cb_pop_clk);
          
              observed_pop_count_gray = cb_pop_clk.pop_valid;
          
              if (observed_pop_count_gray !== expected_push_count_gray) begin
                  $display("Time: %0t, ERROR: test_GrayEncodedCounterSynchronizationPushToPop - Check failed. Expected pop_push_count_gray=0x%h, got 0x%h", $time, expected_push_count_gray, observed_pop_count_gray);
                  test_failed = 1;
              end else begin
                  $display("Time: %0t, INFO: test_GrayEncodedCounterSynchronizationPushToPop - Check passed. Expected value for pop_push_count_gray is the same as the observed value (both are 0x%h).", $time, observed_pop_count_gray);
                  if (test_failed != 1)
                      test_failed = 0;
              end
          end
          
          if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_GrayEncodedCounterSynchronizationPushToPop", $time);
          end else begin
              $display("Time: %0t, FAILED: test_GrayEncodedCounterSynchronizationPushToPop", $time);
          end
      end
    join_any
    disable fork;
  endtask
  
endmodule
  
