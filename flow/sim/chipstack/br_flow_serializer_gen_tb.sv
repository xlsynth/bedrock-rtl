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

module br_flow_serializer_gen_tb;
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

  `include "br_asserts.svh"
  `include "br_asserts_internal.svh"
  `include "br_unused.svh"

  //===========================================================
  // DUT Parameters
  //===========================================================
  parameter int PushWidth = 2;
  parameter int PopWidth = 1;
  parameter int MetadataWidth = 1;
  parameter bit SerializeMostSignificantFirst = 1;
  localparam int SerializationRatio = (PushWidth / PopWidth);
  localparam int SerFlitIdWidth = ((SerializationRatio > 1) ? $clog2(SerializationRatio) : 1);

  //===========================================================
  // Clock and Reset Signals
  //===========================================================
  logic                      clk;
  logic                      rst;

  //===========================================================
  // Other Signals and Variables
  //===========================================================
  logic                      push_valid;
  logic [     PushWidth-1:0] push_data;
  logic                      push_last;
  logic [SerFlitIdWidth-1:0] push_last_dont_care_count;
  logic [ MetadataWidth-1:0] push_metadata;
  logic                      pop_ready;
  logic                      push_ready;
  logic                      pop_valid;
  logic [      PopWidth-1:0] pop_data;
  logic                      pop_last;
  logic [ MetadataWidth-1:0] pop_metadata;

  //===========================================================
  // DUT Instantiation
  //===========================================================
  br_flow_serializer #(
      .PushWidth(PushWidth),
      .PopWidth(PopWidth),
      .MetadataWidth(MetadataWidth),
      .SerializeMostSignificantFirst(SerializeMostSignificantFirst)
  ) dut (
      .clk(clk),
      .rst(rst),
      .push_valid(push_valid),
      .push_data(push_data),
      .push_last(push_last),
      .push_last_dont_care_count(push_last_dont_care_count),
      .push_metadata(push_metadata),
      .pop_ready(pop_ready),
      .push_ready(push_ready),
      .pop_valid(pop_valid),
      .pop_data(pop_data),
      .pop_last(pop_last),
      .pop_metadata(pop_metadata)
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
    inout rst, push_valid, push_data, push_last,
    push_last_dont_care_count, push_metadata, pop_ready;
    input push_ready, pop_valid, pop_data, pop_last, pop_metadata;
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
    cb_clk.push_data <= 'h0;
    cb_clk.push_last <= 'h0;
    cb_clk.push_last_dont_care_count <= 'h0;
    cb_clk.push_metadata <= 'h0;
    cb_clk.pop_ready <= 'h0;

    // Wiggling the reset signal.
    rst = 1'bx;
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
    test_MetadataReplicationScenario();

    reset_dut();
    test_PushReadyHandshakeScenario();

    reset_dut();
    test_PopReadyHandshakeScenario();

    if (overall_tb_status == 1'b0) begin
      $display("TEST FAILED");
      $finish(1);
    end else begin
      $display("TEST PASSED");
      $finish(0);
    end
  end


  task automatic test_MetadataReplicationScenario;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_MetadataReplicationScenario. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_MetadataReplicationScenario. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // Purpose: Verify that metadata is correctly replicated from the push interface to each pop flit.

            // Local variables declaration
            int test_failed = -1;
            logic [PushWidth-1:0] push_data_val;
            logic [MetadataWidth-1:0] push_metadata_val;
            logic [PopWidth-1:0] expected_pop_data;
            logic [MetadataWidth-1:0] expected_pop_metadata;
            int serialization_ratio;
            int i;

            // Initialize local variables
            serialization_ratio = PushWidth / PopWidth;
            push_data_val = $urandom();
            push_metadata_val = $urandom_range(0, (1 << MetadataWidth) - 1);
            expected_pop_metadata = push_metadata_val;

            // Wait for a clock cycle to ensure proper stimulus propagation
            @(cb_clk);

            // Drive initial stimulus
            cb_clk.push_valid <= 1;
            cb_clk.push_data <= push_data_val;
            cb_clk.push_last <= 0;
            cb_clk.push_last_dont_care_count <= 0;
            cb_clk.push_metadata <= push_metadata_val;
            cb_clk.pop_ready <= 1;

            $display($sformatf({"Time: %0t, INFO: test_MetadataReplicationScenario- ",
                                "Driving push_valid=1, push_data=0x%h, push_metadata=0x%h"}, $time,
                                 push_data_val, push_metadata_val));

            // Loop through serialization ratio to check each pop flit
            for (i = 0; i < serialization_ratio; i++) begin
              @(cb_clk);

              // Calculate expected pop_data based on serialization order
              if (SerializeMostSignificantFirst) begin
                expected_pop_data = push_data_val[PushWidth-1-:PopWidth];
                push_data_val = push_data_val << PopWidth;
              end else begin
                expected_pop_data = push_data_val[PopWidth-1:0];
                push_data_val = push_data_val >> PopWidth;
              end

              // Check pop_valid, pop_data, and pop_metadata
              if (cb_clk.pop_valid !== 1 || cb_clk.pop_data !== expected_pop_data ||
              cb_clk.pop_metadata !== expected_pop_metadata) begin
                $display(
                    $sformatf(
                        {"Time: %0t, ERROR: test_MetadataReplicationScenario- ",
                         "Check failed. Expected pop_valid=1, pop_data=0x%h, pop_metadata=0x%h, ",
                         "got pop_valid=%b, pop_data=0x%h, pop_metadata=0x%h"}, $time,
                          expected_pop_data, expected_pop_metadata, pop_valid, pop_data,
                          pop_metadata));
                test_failed = 1;
              end else begin
                $display($sformatf({"Time: %0t, INFO: test_MetadataReplicationScenario- ",
                                    "Check passed. Expected pop_data=0x%h, pop_metadata=0x%h"},
                                     $time, expected_pop_data, expected_pop_metadata));
                if (test_failed != 1) test_failed = 0;
              end
            end

            // Reset stimulus
            @(cb_clk);
            cb_clk.push_valid <= 0;
            cb_clk.push_data <= 0;
            cb_clk.push_last <= 0;
            cb_clk.push_last_dont_care_count <= 0;
            cb_clk.push_metadata <= 0;
            cb_clk.pop_ready <= 0;

            // Report test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_MetadataReplicationScenario", $time);
            end else begin
              $display("Time: %0t, FAILED: test_MetadataReplicationScenario", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushReadyHandshakeScenario;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf(
                     {"Time: %0t, INFO: Timeout: test_PushReadyHandshakeScenario. Stimuli is not ",
                      "observed or it needs more time to finish this test."}, $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_PushReadyHandshakeScenario. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // Purpose: Verify the push-ready handshake mechanism by ensuring that the push interface is ready to accept new data only when the pop interface is ready to receive it.

            // Local variables declaration
            int test_failed = -1;
            logic [PushWidth-1:0] random_push_data;
            logic [MetadataWidth-1:0] random_push_metadata;
            logic [SerFlitIdWidth-1:0] random_push_last_dont_care_count;
            logic random_push_last;
            logic random_pop_ready;

            // Initial delay to ensure proper stimulus propagation
            @(cb_clk);

            // Generate random data for input ports
            random_push_data = $urandom();
            random_push_metadata = $urandom();
            random_push_last_dont_care_count = $urandom_range(0, SerializationRatio - 1);
            random_push_last = $urandom_range(0, 1);
            random_pop_ready = $urandom_range(0, 1);

            // Apply stimulus to DUT inputs
            cb_clk.push_valid <= 1;
            cb_clk.push_data <= random_push_data;
            cb_clk.push_last <= random_push_last;
            cb_clk.push_last_dont_care_count <= random_push_last_dont_care_count;
            cb_clk.push_metadata <= random_push_metadata;
            cb_clk.pop_ready <= random_pop_ready;

            // Display the applied stimulus
            $display($sformatf({"Time: %0t, INFO: test_PushReadyHandshakeScenario - ",
                                "Driving push_valid=1, push_data=0x%h, push_last=%0b, ",
                                "push_last_dont_care_count=%0d, push_metadata=0x%h, pop_ready=%0b"
                                 }, $time, random_push_data, random_push_last,
                                 random_push_last_dont_care_count, random_push_metadata,
                                 random_pop_ready));

            // Wait for a clock cycle to allow the DUT to process the inputs
            @(cb_clk);

            // Check the push_ready signal based on pop_ready
            if (random_pop_ready && cb_clk.push_ready !== 1) begin
              $display(
                  $sformatf(
                      {"Time: %0t, ERROR: test_PushReadyHandshakeScenario - ",
                       "Check failed. Expected push_ready=1 when pop_ready=1, got push_ready=%0b"},
                        $time, cb_clk.push_ready));
              test_failed = 1;
            end else if (!random_pop_ready && cb_clk.push_ready !== 0) begin
              $display(
                  $sformatf(
                      {"Time: %0t, ERROR: test_PushReadyHandshakeScenario - ",
                       "Check failed. Expected push_ready=0 when pop_ready=0, got push_ready=%0b"},
                        $time, cb_clk.push_ready));
              test_failed = 1;
            end else begin
              $display($sformatf({"Time: %0t, INFO: test_PushReadyHandshakeScenario - ",
                                  "Check passed. push_ready=%0b as expected with pop_ready=%0b"},
                                   $time, cb_clk.push_ready, random_pop_ready));
              if (test_failed != 1) test_failed = 0;
            end

            // Final test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_PushReadyHandshakeScenario", $time);
            end else begin
              $display("Time: %0t, FAILED: test_PushReadyHandshakeScenario", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopReadyHandshakeScenario;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display($sformatf({"Time: %0t, INFO: Timeout: test_PopReadyHandshakeScenario. ",
                            "Stimuli is not observed or it needs more time to finish this test."},
                             $time));
      end
      begin
        fork
          begin
            #(PER_TASK_TIMEOUT);
            $display($sformatf({"Time: %0t, INFO: Timeout: test_PopReadyHandshakeScenario. ",
                                "Stimuli is not observed or it needs more time to finish this test."
                                 }, $time));
          end
          begin
            // This task tests the Pop-Ready Handshake scenario, ensuring that data is only sent when the receiving side is ready.
            // Local variables declaration
            int test_failed = -1;
            logic [PushWidth-1:0] random_push_data;
            logic [MetadataWidth-1:0] random_push_metadata;
            logic [SerFlitIdWidth-1:0] random_push_last_dont_care_count;
            logic random_push_last;
            logic random_push_valid;
            logic random_pop_ready;
            logic [PopWidth-1:0] expected_pop_data;
            logic [MetadataWidth-1:0] expected_pop_metadata;
            logic expected_pop_last;
            logic expected_pop_valid;
            int serialization_counter;
            int i;

            // Initial setup
            @(cb_clk);
            random_push_data = $urandom();
            random_push_metadata = $urandom();
            random_push_last_dont_care_count = $urandom_range(0, SerializationRatio - 1);
            random_push_last = $urandom_range(0, 1);
            random_push_valid = 1'b1;
            random_pop_ready = 1'b1;
            serialization_counter = 0;

            // Apply initial stimulus
            cb_clk.push_valid <= random_push_valid;
            cb_clk.push_data <= random_push_data;
            cb_clk.push_last <= random_push_last;
            cb_clk.push_last_dont_care_count <= random_push_last_dont_care_count;
            cb_clk.push_metadata <= random_push_metadata;
            cb_clk.pop_ready <= random_pop_ready;

            // Wait for push_ready to be asserted
            @(cb_clk);
            while (!cb_clk.push_ready) begin
              @(cb_clk);
            end

            // Start serialization process
            for (i = 0; i < SerializationRatio; i++) begin
              @(cb_clk);
              if (random_pop_ready && cb_clk.pop_valid) begin
                // Calculate expected pop_data and pop_metadata
                if (SerializeMostSignificantFirst) begin
                  expected_pop_data =
                  random_push_data >> ((SerializationRatio - 1 - serialization_counter) * PopWidth);
                end else begin
                  expected_pop_data = random_push_data >> (serialization_counter * PopWidth);
                end
                expected_pop_metadata = random_push_metadata;
                expected_pop_last = (
                  random_push_last &&
                  (serialization_counter ==
                  (SerializationRatio - random_push_last_dont_care_count - 1)));
                expected_pop_valid = 1'b1;

                // Check pop_data, pop_metadata, pop_last, and pop_valid
                if ((cb_clk.pop_data !== expected_pop_data) ||
                (cb_clk.pop_metadata !== expected_pop_metadata) ||
                        (cb_clk.pop_last !== expected_pop_last) ||
                        (cb_clk.pop_valid !== expected_pop_valid)) begin
                  $display(
                      $sformatf(
                          {"Time: %0t, ERROR: test_PopReadyHandshakeScenario - ",
                           "Check failed. Expected pop_data=0x%h, pop_metadata=0x%h, ",
                           "pop_last=%b, pop_valid=%b; got pop_data=0x%h, pop_metadata=0x%h, pop_last=%b, pop_valid=%b"
                            }, $time, expected_pop_data, expected_pop_metadata, expected_pop_last,
                            expected_pop_valid, cb_clk.pop_data, cb_clk.pop_metadata,
                            cb_clk.pop_last, cb_clk.pop_valid));
                  test_failed = 1;
                end else begin
                  $display($sformatf({"Time: %0t, INFO: test_PopReadyHandshakeScenario - ",
                                      "Check passed. Expected values match observed values."},
                                       $time));
                  if (test_failed != 1) test_failed = 0;
                end

                // Increment serialization counter
                serialization_counter++;
              end
            end

            // Final test status
            if (test_failed == 0) begin
              $display("Time: %0t, PASSED: test_PopReadyHandshakeScenario", $time);
            end else begin
              $display("Time: %0t, FAILED: test_PopReadyHandshakeScenario", $time);
              overall_tb_status = 0;
            end
          end
        join_any
        disable fork;
      end
    join_any
    disable fork;
  endtask


  asrt_push_valid_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(push_valid));

  asrt_push_data_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(push_data));

  asrt_push_last_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(push_last));

  asrt_push_last_dont_care_count_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(
      push_last_dont_care_count
  ));

  asrt_push_metadata_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(push_metadata));

  asrt_pop_ready_not_unknown :
  assert property (@(posedge clk) disable iff (rst !== 1'b0) !$isunknown(pop_ready));

endmodule
