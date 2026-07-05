// SPDX-License-Identifier: Apache-2.0

// Bedrock-RTL Flow Serializer/Deserializer Testbench
//
// Test plan: check serializer ordering for full and shortened last push flits,
// including that last-don't-care count is ignored for non-last push flits,
// then check deserializer reconstruction for a full pop flit and an early-last
// partial pop flit. Stall each direction once to check state hold under
// backpressure. The suite sweeps most-significant-first and least-significant-
// first ordering so both slice directions and last-dont-care accounting are covered.

module br_flow_serializer_tb;
  parameter bit SerializeMostSignificantFirst = 0;

  localparam int PushWidth = 16;
  localparam int PopWidth = 4;
  localparam int MetadataWidth = 3;
  localparam int Ratio = PushWidth / PopWidth;
  localparam int FlitIdWidth = $clog2(Ratio);

  logic clk;
  logic rst;

  logic ser_push_ready;
  logic ser_push_valid;
  logic [PushWidth-1:0] ser_push_data;
  logic ser_push_last;
  logic [FlitIdWidth-1:0] ser_push_last_dont_care_count;
  logic [MetadataWidth-1:0] ser_push_metadata;
  logic ser_pop_ready;
  logic ser_pop_valid;
  logic [PopWidth-1:0] ser_pop_data;
  logic ser_pop_last;
  logic [MetadataWidth-1:0] ser_pop_metadata;

  logic deser_push_ready;
  logic deser_push_valid;
  logic [PopWidth-1:0] deser_push_data;
  logic deser_push_last;
  logic [MetadataWidth-1:0] deser_push_metadata;
  logic deser_pop_ready;
  logic deser_pop_valid;
  logic [PushWidth-1:0] deser_pop_data;
  logic deser_pop_last;
  logic [FlitIdWidth-1:0] deser_pop_last_dont_care_count;
  logic [MetadataWidth-1:0] deser_pop_metadata;

  br_flow_serializer #(
      .PushWidth(PushWidth),
      .PopWidth(PopWidth),
      .MetadataWidth(MetadataWidth),
      .SerializeMostSignificantFirst(SerializeMostSignificantFirst)
  ) br_flow_serializer (
      .clk,
      .rst,
      .push_ready(ser_push_ready),
      .push_valid(ser_push_valid),
      .push_data(ser_push_data),
      .push_last(ser_push_last),
      .push_last_dont_care_count(ser_push_last_dont_care_count),
      .push_metadata(ser_push_metadata),
      .pop_ready(ser_pop_ready),
      .pop_valid(ser_pop_valid),
      .pop_data(ser_pop_data),
      .pop_last(ser_pop_last),
      .pop_metadata(ser_pop_metadata)
  );

  br_flow_deserializer #(
      .PushWidth(PopWidth),
      .PopWidth(PushWidth),
      .MetadataWidth(MetadataWidth),
      .DeserializeMostSignificantFirst(SerializeMostSignificantFirst)
  ) br_flow_deserializer (
      .clk,
      .rst,
      .push_ready(deser_push_ready),
      .push_valid(deser_push_valid),
      .push_data(deser_push_data),
      .push_last(deser_push_last),
      .push_metadata(deser_push_metadata),
      .pop_ready(deser_pop_ready),
      .pop_valid(deser_pop_valid),
      .pop_data(deser_pop_data),
      .pop_last(deser_pop_last),
      .pop_last_dont_care_count(deser_pop_last_dont_care_count),
      .pop_metadata(deser_pop_metadata)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic logic [PopWidth-1:0] slice(input logic [PushWidth-1:0] data, input int flit);
    int slice_id;
    slice_id = SerializeMostSignificantFirst ? (Ratio - 1 - flit) : flit;
    return data[(slice_id*PopWidth)+:PopWidth];
  endfunction

  task automatic check_flit(input logic [PopWidth-1:0] actual, input logic [PopWidth-1:0] expected,
                            input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got 0x%0h, expected 0x%0h", message, actual, expected);
    end
  endtask

  task automatic check_packet(input logic [PushWidth-1:0] actual,
                              input logic [PushWidth-1:0] expected, input string message);
    if (actual !== expected) begin
      td.error_count++;
      $error("%s: got 0x%0h, expected 0x%0h", message, actual, expected);
    end
  endtask

  task automatic send_serializer_word(input logic [PushWidth-1:0] data, input logic last,
                                      input logic [FlitIdWidth-1:0] dont_care_count,
                                      input int expected_flits, input logic stall_second_flit);
    ser_push_valid = 1'b1;
    ser_push_data = data;
    ser_push_last = last;
    ser_push_last_dont_care_count = dont_care_count;

    for (int flit = 0; flit < expected_flits; flit++) begin
      if (stall_second_flit && flit == 1) begin
        ser_pop_ready = 1'b0;
        #1;
        td.check(ser_pop_valid, "serializer should retain pop_valid while stalled");
        check_flit(ser_pop_data, slice(data, flit), "serializer stalled pop_data");
        td.check(!ser_push_ready, "serializer should not complete while stalled");
        @(posedge clk);
        #1;
        check_flit(ser_pop_data, slice(data, flit), "serializer stalled pop_data hold");
        ser_pop_ready = 1'b1;
      end
      #1;
      td.check(ser_pop_valid, "serializer pop_valid should be asserted");
      check_flit(ser_pop_data, slice(data, flit), "serializer pop_data");
      td.check(ser_pop_metadata == ser_push_metadata, "serializer metadata mismatch");
      td.check(ser_pop_last == (last && flit == expected_flits - 1),
               "serializer pop_last mismatch");
      if (flit == expected_flits - 1) begin
        td.check(ser_push_ready, "serializer push_ready should complete on final flit");
      end else begin
        td.check(!ser_push_ready, "serializer push_ready should wait for final flit");
      end
      @(posedge clk);
      #1;
    end

    ser_push_valid = 1'b0;
    ser_push_last = 1'b0;
    ser_push_last_dont_care_count = '0;
    @(negedge clk);
  endtask

  task automatic check_partial_packet(input logic [PushWidth-1:0] expected,
                                      input int expected_flits);
    int slice_id;
    for (int flit = 0; flit < expected_flits; flit++) begin
      slice_id = SerializeMostSignificantFirst ? (Ratio - 1 - flit) : flit;
      check_flit(deser_pop_data[(slice_id*PopWidth)+:PopWidth], slice(expected, flit),
                 "deserializer partial pop_data");
    end
  endtask

  task automatic send_deserializer_flit(input logic [PopWidth-1:0] data, input logic last,
                                        input logic [MetadataWidth-1:0] metadata);
    deser_push_valid = 1'b1;
    deser_push_data = data;
    deser_push_last = last;
    deser_push_metadata = metadata;
    #1;
    td.check(deser_push_ready, "deserializer push_ready should accept flit");
  endtask

  initial begin
    ser_push_valid = 1'b0;
    ser_push_data = '0;
    ser_push_last = 1'b0;
    ser_push_last_dont_care_count = '0;
    ser_push_metadata = 3'h5;
    ser_pop_ready = 1'b1;
    deser_push_valid = 1'b0;
    deser_push_data = '0;
    deser_push_last = 1'b0;
    deser_push_metadata = '0;
    deser_pop_ready = 1'b1;

    td.reset_dut();

    send_serializer_word(16'habcd, 1'b0, '0, 4, 1'b1);
    send_serializer_word(16'h5678, 1'b0, 2'd2, 4, 1'b0);
    send_serializer_word(16'h1234, 1'b1, 2'd1, 3, 1'b0);

    send_deserializer_flit(slice(16'habcd, 0), 1'b0, 3'h2);
    @(posedge clk);
    #1;
    send_deserializer_flit(slice(16'habcd, 1), 1'b0, 3'h2);
    @(posedge clk);
    #1;
    send_deserializer_flit(slice(16'habcd, 2), 1'b0, 3'h2);
    @(posedge clk);
    #1;
    send_deserializer_flit(slice(16'habcd, 3), 1'b0, 3'h2);
    #1;
    td.check(deser_pop_valid, "deserializer full pop_valid");
    check_packet(deser_pop_data, 16'habcd, "deserializer full pop_data");
    td.check(!deser_pop_last, "deserializer full pop_last should be zero");
    td.check(deser_pop_metadata == 3'h2, "deserializer full metadata");
    @(posedge clk);
    #1;

    send_deserializer_flit(slice(16'h1234, 0), 1'b0, 3'h6);
    @(posedge clk);
    #1;
    send_deserializer_flit(slice(16'h1234, 1), 1'b0, 3'h6);
    @(posedge clk);
    #1;
    deser_pop_ready = 1'b0;
    deser_push_valid = 1'b1;
    deser_push_data = slice(16'h1234, 2);
    deser_push_last = 1'b1;
    deser_push_metadata = 3'h6;
    #1;
    td.check(deser_pop_valid, "deserializer partial pop_valid");
    td.check(deser_pop_last, "deserializer partial pop_last");
    td.check(deser_pop_last_dont_care_count == 2'd1, "deserializer dont-care count");
    td.check(deser_pop_metadata == 3'h6, "deserializer partial metadata");
    td.check(!deser_push_ready, "deserializer should stall completed output");
    check_partial_packet(16'h1234, 3);
    @(posedge clk);
    #1;
    td.check(deser_pop_valid, "deserializer should retain partial pop_valid while stalled");
    td.check(deser_pop_last, "deserializer should retain partial pop_last while stalled");
    check_partial_packet(16'h1234, 3);
    deser_pop_ready = 1'b1;
    #1;
    td.check(deser_push_ready, "deserializer should complete when output stall clears");
    @(posedge clk);
    #1;

    ser_push_valid   = 1'b0;
    deser_push_valid = 1'b0;
    deser_push_last  = 1'b0;
    td.finish();
  end

endmodule
