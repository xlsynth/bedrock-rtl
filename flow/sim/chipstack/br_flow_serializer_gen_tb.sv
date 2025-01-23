//=============================================================
// Testbench for Module: br_flow_serializer
//=============================================================
// Author: ChipStack AI
// Date: 2025-01-20 18:25:27
// Description: Unit test for br_flow_serializer
//=============================================================

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
  int test_failed = -1;

  //===========================================================
  // Clock Generation
  //===========================================================
  initial begin
    clk = 1'b0;
    forever #(CLOCK_FREQ_NS_CONVERSION_FACTOR / (2 * CLOCK_FREQ)) clk = ~clk;
  end
  clocking cb_clk @(posedge clk);
    default input #1step output #4;
    inout rst, push_valid, push_data, push_last, push_last_dont_care_count,
          push_metadata, pop_ready;
    input push_ready, pop_valid, pop_data, pop_last, pop_metadata;
  endclocking


  //===========================================================
  // Timeout Control
  //===========================================================
  initial begin
    if (NO_ASSERTS_ON_RESET) $assertoff;
    #(TIMEOUT);
    $display({"Error: Testbench timeout!"});
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
    test_DataSerialization();

    reset_dut();
    test_HandlingDontCareValues();

    reset_dut();
    test_MetadataReplication();

    reset_dut();
    test_PushReadyHandshake();

    reset_dut();
    test_PopReadyHandshake();

    $finish;
  end


  task automatic test_DataSerialization;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_DataSerialization. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the serialization of wide packet flits from the push interface onto a narrower pop interface.
        // Local variables declaration
        int test_failed = -1;
        logic [PopWidth-1:0] expected_pop_data;
        logic [MetadataWidth-1:0] expected_pop_metadata;
        logic expected_pop_last;
        int serialization_ratio = SerializationRatio;
        int i;

        // Initialize inputs
        cb_clk.push_valid <= 1'b0;
        cb_clk.push_data <= '0;
        cb_clk.push_last <= 1'b0;
        cb_clk.push_last_dont_care_count <= '0;
        cb_clk.push_metadata <= '0;
        cb_clk.pop_ready <= 1'b1;

        // Wait for a clock cycle to ensure proper initialization
        @(cb_clk);

        // Start the test by asserting push_valid and providing data
        cb_clk.push_valid <= 1'b1;
        cb_clk.push_data <= $urandom();
        cb_clk.push_last <= 1'b1;
        cb_clk.push_last_dont_care_count <= $urandom_range(0, serialization_ratio - 1);
        cb_clk.push_metadata <= $urandom();
        cb_clk.pop_ready <= 1'b1;

        // Calculate expected values based on the serialization order
        for (i = 0; i < serialization_ratio; i++) begin
          if (SerializeMostSignificantFirst) begin
            expected_pop_data = cb_clk.push_data[PushWidth-1-i*PopWidth-:PopWidth];
          end else begin
            expected_pop_data = cb_clk.push_data[i*PopWidth+:PopWidth];
          end
          expected_pop_metadata = cb_clk.push_metadata;
          expected_pop_last = (i == (serialization_ratio - cb_clk.push_last_dont_care_count - 1)) ?
                              1'b1 : 1'b0;

          // Apply stimulus and check outputs
          @(cb_clk);
          if (cb_clk.pop_valid !== 1'b1 || cb_clk.pop_data !== expected_pop_data ||
              cb_clk.pop_metadata !== expected_pop_metadata ||
              cb_clk.pop_last !== expected_pop_last) begin
            $display({"Time: %0t, ERROR: test_DataSerialization - Check failed. ",
                      "Expected pop_valid=1, pop_data=0x%h, pop_metadata=0x%h, pop_last=%b; got ",
                      "pop_valid=%b, pop_data=0x%h, pop_metadata=0x%h, pop_last=%b"}, $time,
                       expected_pop_data, expected_pop_metadata, expected_pop_last,
                       cb_clk.pop_valid, cb_clk.pop_data, cb_clk.pop_metadata, cb_clk.pop_last);
            test_failed = 1;
          end else begin
            $display(
                {"Time: %0t, INFO: test_DataSerialization - Check passed. ",
                 "Expected pop_data=0x%h, pop_metadata=0x%h, pop_last=%b; observed pop_data=0x%h, ",
                 "pop_metadata=0x%h, pop_last=%b"}, $time, expected_pop_data, expected_pop_metadata,
                  expected_pop_last, cb_clk.pop_data, cb_clk.pop_metadata, cb_clk.pop_last);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Reset inputs
        cb_clk.push_valid <= 1'b0;
        cb_clk.push_data <= '0;
        cb_clk.push_last <= 1'b0;
        cb_clk.push_last_dont_care_count <= '0;
        cb_clk.push_metadata <= '0;
        cb_clk.pop_ready <= 1'b0;

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_DataSerialization"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_DataSerialization"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_HandlingDontCareValues;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_HandlingDontCareValues. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the handling of 'don't care' values in the last flit of a packet.
        // It ensures that unnecessary data is not transmitted, optimizing the data flow.

        // Local variables declaration
        int test_failed = -1;
        int i;
        logic [PushWidth-1:0] push_data_value;
        logic [MetadataWidth-1:0] push_metadata_value;
        logic [SerFlitIdWidth-1:0] push_last_dont_care_count_value;
        logic [PopWidth-1:0] expected_pop_data;
        logic [MetadataWidth-1:0] expected_pop_metadata;
        logic expected_pop_last;
        int valid_segments;

        // Initialize variables
        push_data_value = $urandom();
        push_metadata_value = $urandom();
        push_last_dont_care_count_value = $urandom_range(0, SerializationRatio - 1);
        valid_segments = SerializationRatio - push_last_dont_care_count_value;

        // Apply stimulus
        @(cb_clk);
        cb_clk.push_valid <= 1;
        cb_clk.push_data <= push_data_value;
        cb_clk.push_last <= 1;
        cb_clk.push_last_dont_care_count <= push_last_dont_care_count_value;
        cb_clk.push_metadata <= push_metadata_value;
        cb_clk.pop_ready <= 1;
        $display({"Time: %0t, INFO: test_HandlingDontCareValues - Driving push_valid=1, ",
                  "push_data=0x%h, push_last=1, push_last_dont_care_count=%0d, push_metadata=0x%h"},
                   $time, push_data_value, push_last_dont_care_count_value, push_metadata_value);

        // Wait for push_ready to be asserted
        @(cb_clk);
        while (!cb_clk.push_ready) begin
          @(cb_clk);
        end

        // Check serialized output
        for (i = 0; i < valid_segments; i++) begin
          @(cb_clk);
          expected_pop_data = (SerializeMostSignificantFirst) ?
                              push_data_value[PushWidth-1 - i*PopWidth -: PopWidth] :
                              push_data_value[i*PopWidth +: PopWidth];
          expected_pop_metadata = push_metadata_value;
          expected_pop_last = (i == valid_segments - 1);

          if (cb_clk.pop_valid && cb_clk.pop_data == expected_pop_data &&
              cb_clk.pop_metadata == expected_pop_metadata &&
              cb_clk.pop_last == expected_pop_last) begin
            $display(
                {"Time: %0t, INFO: test_HandlingDontCareValues - Check passed for segment %0d. ",
                 "Expected pop_data=0x%h, pop_metadata=0x%h, pop_last=%0b"}, $time, i,
                  expected_pop_data, expected_pop_metadata, expected_pop_last);
            if (test_failed != 1) test_failed = 0;
          end else begin
            $display(
                {"Time: %0t, ERROR: test_HandlingDontCareValues - Check failed for segment %0d. ",
                 "Expected pop_data=0x%h, pop_metadata=0x%h, pop_last=%0b, got pop_data=0x%h, ",
                 "pop_metadata=0x%h, pop_last=%0b"}, $time, i, expected_pop_data,
                  expected_pop_metadata, expected_pop_last, pop_data, pop_metadata, pop_last);
            test_failed = 1;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_HandlingDontCareValues"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_HandlingDontCareValues"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_MetadataReplication;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_MetadataReplication. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the Metadata Replication functionality of the br_flow_serializer module.
        // It verifies that the metadata provided on the push interface is correctly replicated on each pop flit.

        // Local variables declaration
        int test_failed = -1;
        logic [PopWidth-1:0] expected_pop_data;
        logic [MetadataWidth-1:0] expected_pop_metadata;
        int i;

        // Initialize variables
        cb_clk.push_data <= $urandom();
        cb_clk.push_metadata <= $urandom_range(0, (1 << MetadataWidth) - 1);
        expected_pop_metadata = cb_clk.push_metadata;

        // Wait for a clock cycle to ensure proper stimulus propagation
        @(cb_clk);

        // Apply stimulus
        cb_clk.push_valid <= 1;
        cb_clk.push_data <= push_data;
        cb_clk.push_last <= 0;
        cb_clk.push_last_dont_care_count <= 0;
        cb_clk.push_metadata <= push_metadata;
        cb_clk.pop_ready <= 1;

        // Display the applied stimulus
        $display({"Time: %0t, INFO: test_MetadataReplication - Driving push_valid=1, ",
                  "push_data=0x%h, push_metadata=0x%h"}, $time, push_data, push_metadata);

        // Wait for the serialization process to complete
        for (i = 0; i < SerializationRatio; i++) begin
          @(cb_clk);

          // Calculate expected pop_data based on serialization order
          if (SerializeMostSignificantFirst) begin
            expected_pop_data = cb_clk.push_data[PushWidth-1-i*PopWidth-:PopWidth];
          end else begin
            expected_pop_data = cb_clk.push_data[i*PopWidth+:PopWidth];
          end

          // Check pop_valid and pop_metadata
          if (cb_clk.pop_valid && cb_clk.pop_metadata == expected_pop_metadata) begin
            $display({"Time: %0t, INFO: test_MetadataReplication - Check passed. ",
                      "pop_metadata=0x%h matches expected=0x%h"}, $time, pop_metadata,
                       expected_pop_metadata);
            if (test_failed != 1) test_failed = 0;
          end else begin
            $display({"Time: %0t, ERROR: test_MetadataReplication - Check failed. ",
                      "pop_metadata=0x%h, expected=0x%h"}, $time, pop_metadata,
                       expected_pop_metadata);
            test_failed = 1;
          end

          // Check pop_data
          if (cb_clk.pop_data == expected_pop_data) begin
            $display({"Time: %0t, INFO: test_MetadataReplication - Check passed. ",
                      "pop_data=0x%h matches expected=0x%h"}, $time, pop_data, expected_pop_data);
            if (test_failed != 1) test_failed = 0;
          end else begin
            $display({"Time: %0t, ERROR: test_MetadataReplication - Check failed. ",
                      "pop_data=0x%h, expected=0x%h"}, $time, pop_data, expected_pop_data);
            test_failed = 1;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_MetadataReplication"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_MetadataReplication"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PushReadyHandshake;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PushReadyHandshake. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the Push-Ready Handshake functionality, ensuring that the push interface is ready to accept new data by managing the `push_ready` signal. It verifies that data is only sent when the receiving side is ready, adhering to the ready-valid handshake protocol.

        // Local variables declaration
        int test_failed = -1;
        logic [PushWidth-1:0] random_push_data;
        logic [MetadataWidth-1:0] random_push_metadata;
        logic [SerFlitIdWidth-1:0] random_push_last_dont_care_count;
        logic random_push_last;
        logic random_pop_ready;
        int i;

        // Initial delay to ensure proper setup
        @(cb_clk);

        // Test scenario: Drive push_valid high and monitor push_ready
        for (i = 0; i < 10; i++) begin
          // Generate random values for inputs
          random_push_data = $urandom();
          random_push_metadata = $urandom();
          random_push_last_dont_care_count = $urandom_range(0, SerializationRatio - 1);
          random_push_last = $urandom_range(0, 1);
          random_pop_ready = $urandom_range(0, 1);

          // Apply stimulus
          cb_clk.push_valid <= 1;
          cb_clk.push_data <= random_push_data;
          cb_clk.push_metadata <= random_push_metadata;
          cb_clk.push_last <= random_push_last;
          cb_clk.push_last_dont_care_count <= random_push_last_dont_care_count;
          cb_clk.pop_ready <= random_pop_ready;

          // Display applied stimulus
          $display({"Time: %0t, INFO: test_PushReadyHandshake - Driving push_valid=1, ",
                    "push_data=0x%h, push_metadata=0x%h, push_last=%0b, ",
                    "push_last_dont_care_count=%0d, pop_ready=%0b"}, $time, random_push_data,
                     random_push_metadata, random_push_last, random_push_last_dont_care_count,
                     random_pop_ready);

          // Wait for a clock cycle
          @(cb_clk);

          // Check the push_ready signal
          if (random_pop_ready && cb_clk.push_ready !== 1) begin
            $display({"Time: %0t, ERROR: test_PushReadyHandshake - Check failed. ",
                      "Expected push_ready=1, got push_ready=%0b"}, $time, cb_clk.push_ready);
            test_failed = 1;
          end else if (!random_pop_ready && cb_clk.push_ready !== 0) begin
            $display({"Time: %0t, ERROR: test_PushReadyHandshake - Check failed. ",
                      "Expected push_ready=0, got push_ready=%0b"}, $time, cb_clk.push_ready);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PushReadyHandshake - Check passed. ",
                      "push_ready=%0b as expected."}, $time, cb_clk.push_ready);
            if (test_failed != 1) test_failed = 0;
          end

          // Random delay between operations
          repeat ($urandom_range(1, 3)) @(cb_clk);

          // Disable further stimulus application
          cb_clk.push_valid <= 0;
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PushReadyHandshake"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PushReadyHandshake"}, $time);
        end
      end
    join_any
    disable fork;
  endtask


  task automatic test_PopReadyHandshake;
    fork
      begin
        #(PER_TASK_TIMEOUT);
        $display({"Time: %0t, INFO: Timeout: test_PopReadyHandshake. ",
                  "Stimuli is not observed or it needs more time to finish this test."}, $time);
      end
      begin
        // This task tests the Pop-Ready Handshake functionality of the br_flow_serializer module.
        // It ensures that data is only sent when the pop interface is ready, adhering to the ready-valid handshake protocol.

        // Local variables declaration
        int test_failed = -1;
        logic [PopWidth-1:0] expected_pop_data;
        logic [MetadataWidth-1:0] expected_pop_metadata;
        logic expected_pop_last;
        int serialization_count;
        int i;

        // Initialize local variables
        cb_clk.push_data <= $urandom();
        cb_clk.push_metadata <= $urandom();
        serialization_count = SerializationRatio;
        expected_pop_last   = 0;

        // Wait for a clock cycle to ensure proper stimulus propagation
        @(cb_clk);

        // Drive initial stimulus
        cb_clk.push_valid <= 1;
        cb_clk.push_data <= push_data;
        cb_clk.push_last <= 0;
        cb_clk.push_last_dont_care_count <= 0;
        cb_clk.push_metadata <= push_metadata;
        cb_clk.pop_ready <= 1;

        $display({"Time: %0t, INFO: test_PopReadyHandshake - Initial stimulus applied. ",
                  "push_data=0x%h, push_metadata=0x%h"}, $time, push_data, push_metadata);

        // Loop through serialization process
        for (i = 0; i < serialization_count; i++) begin
          @(cb_clk);

          // Calculate expected pop_data based on serialization order
          if (SerializeMostSignificantFirst) begin
            expected_pop_data = cb_clk.push_data[PushWidth-1-i*PopWidth-:PopWidth];
          end else begin
            expected_pop_data = cb_clk.push_data[i*PopWidth+:PopWidth];
          end

          expected_pop_metadata = cb_clk.push_metadata;

          // Check pop_valid and pop_data
          if (cb_clk.pop_valid !== 1 || cb_clk.pop_data !== expected_pop_data) begin
            $display({"Time: %0t, ERROR: test_PopReadyHandshake - Check failed. ",
                      "Expected pop_data=0x%h, got pop_data=0x%h"}, $time, expected_pop_data,
                       pop_data);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PopReadyHandshake - Check passed. ",
                      "Expected pop_data=0x%h is the same as observed pop_data=0x%h."}, $time,
                       expected_pop_data, pop_data);
            if (test_failed != 1) test_failed = 0;
          end

          // Check pop_metadata
          if (cb_clk.pop_metadata !== expected_pop_metadata) begin
            $display({"Time: %0t, ERROR: test_PopReadyHandshake - Check failed. ",
                      "Expected pop_metadata=0x%h, got pop_metadata=0x%h"}, $time,
                       expected_pop_metadata, pop_metadata);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PopReadyHandshake - Check passed. ",
                      "Expected pop_metadata=0x%h is the same as observed pop_metadata=0x%h."},
                       $time, expected_pop_metadata, pop_metadata);
            if (test_failed != 1) test_failed = 0;
          end

          // Check pop_last
          if (i == serialization_count - 1) begin
            expected_pop_last = 1;
          end else begin
            expected_pop_last = 0;
          end

          if (cb_clk.pop_last !== expected_pop_last) begin
            $display({"Time: %0t, ERROR: test_PopReadyHandshake - Check failed. ",
                      "Expected pop_last=%0b, got pop_last=%0b"}, $time, expected_pop_last,
                       pop_last);
            test_failed = 1;
          end else begin
            $display({"Time: %0t, INFO: test_PopReadyHandshake - Check passed. ",
                      "Expected pop_last=%0b is the same as observed pop_last=%0b."}, $time,
                       expected_pop_last, pop_last);
            if (test_failed != 1) test_failed = 0;
          end
        end

        // Final test status
        if (test_failed == 0) begin
          $display({"Time: %0t, PASSED: test_PopReadyHandshake"}, $time);
        end else begin
          $display({"Time: %0t, FAILED: test_PopReadyHandshake"}, $time);
        end
      end
    join_any
    disable fork;
  endtask

endmodule
