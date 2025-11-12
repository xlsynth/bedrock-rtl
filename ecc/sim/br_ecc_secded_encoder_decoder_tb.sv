// SPDX-License-Identifier: Apache-2.0



// Testbench for br_ecc_secded_encoder and br_ecc_secded_decoder

`timescale 1ns / 1ps

module br_ecc_secded_encoder_decoder_tb;

  // Parameters
  parameter int DataWidth = 8;
  localparam int ParityWidth = br_ecc_secded::get_parity_width(DataWidth);
  localparam int MessageWidth = br_ecc_secded::get_message_width(DataWidth, ParityWidth);
  localparam int CodewordWidth = MessageWidth + ParityWidth;
  // Separate RegisterOutputs parameters for encoder and decoder
  parameter bit EncoderRegisterInputs = 0;
  parameter bit EncoderRegisterOutputs = 0;
  parameter bit DecoderRegisterInputs = 0;
  parameter bit DecoderRegisterSyndrome = 0;
  parameter bit DecoderRegisterOutputs = 0;

  // TODO: have TB support E2E latency > 0
  localparam int E2ELatency =
      int'(EncoderRegisterInputs) +
      int'(EncoderRegisterOutputs) +
      int'(DecoderRegisterInputs) +
      int'(DecoderRegisterSyndrome) +
      int'(DecoderRegisterOutputs);

  // Clock and reset
  logic clk;
  logic rst;

  // Encoder inputs
  logic data_valid;
  logic [DataWidth-1:0] data;

  // Encoder outputs
  logic enc_valid;
  logic [DataWidth-1:0] enc_data;
  logic [ParityWidth-1:0] enc_parity;

  // Point of error injection. ChannelWidth <= CodewordWidth because if DataWidth < MessageWidth
  // there are 0 pads that are not transmitted from encoder to decoder.
  localparam int ChannelWidth = DataWidth + ParityWidth;
  logic [ChannelWidth-1:0] pre_inject;
  logic [ChannelWidth-1:0] injected;
  logic [DataWidth-1:0] rcv_data;
  logic [ParityWidth-1:0] rcv_parity;

  // Decoder outputs
  logic dec_valid;
  logic [DataWidth-1:0] dec_data;
  logic dec_error_ce;
  logic dec_error_due;
  logic [ParityWidth-1:0] dec_error_syndrome;

  // Instantiate encoder
  br_ecc_secded_encoder #(
      .DataWidth(DataWidth),
      .RegisterInputs(EncoderRegisterInputs),
      .RegisterOutputs(EncoderRegisterOutputs)
  ) br_ecc_secded_encoder (
      .clk,
      .rst,
      .data_valid,
      .data,
      .enc_valid,
      .enc_codeword(),  // unused
      .enc_data,
      .enc_parity
  );

  assign pre_inject = {enc_parity, enc_data};
  assign {rcv_parity, rcv_data} = injected;

  // Instantiate decoder (inputs connected directly to encoder outputs)
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .RegisterInputs(DecoderRegisterInputs),
      .RegisterSyndrome(DecoderRegisterSyndrome),
      .RegisterOutputs(DecoderRegisterOutputs)
  ) br_ecc_secded_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_data,
      .rcv_parity,
      .dec_valid,
      .dec_codeword(),  // unused
      .dec_data,
      .dec_error_ce,
      .dec_error_due,
      .dec_error_syndrome
  );

  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;  // 100MHz clock

  // Test process
  logic [DataWidth-1:0] test_data;
  int num_tests = 1000;
  int num_double_bit_injections_per_test = 10;
  int i;
  int error_counter = 0;
  int inj_index0 = -1;
  int inj_index1 = -1;

  initial begin
    rst = 1;
    data_valid = 0;
    data = 0;
    injected = 0;
    repeat (10) @(negedge clk);
    rst = 0;
    repeat (10) @(negedge clk);

    $display("Testing without error injection.");
    for (i = 0; i < num_tests; i = i + 1) begin
      test_data = $urandom;

      // Apply data to encoder at negedge clk
      // TODO: this only works when E2ELatency is 0.
      @(negedge clk);
      data_valid = 1;
      data = test_data;
      #1;
      // Propagate the codeword to the decoder
      injected = pre_inject;
      #1;
      if (!dec_valid) begin
        $error("Test %0d FAILED: no dec_valid", i);
        error_counter = error_counter + 1;
      end
      if (dec_data !== test_data) begin
        $error("Test %0d FAILED: encoded data = 0x%0h, decoded data = 0x%0h", i, test_data,
               dec_data);
        error_counter = error_counter + 1;
      end
      if (dec_error_ce) begin
        $error("Test %0d FAILED: error corrected when it was not supposed to", i);
        error_counter = error_counter + 1;
      end
      if (dec_error_due) begin
        $error("Test %0d FAILED: error DUE when it was not supposed to", i);
        error_counter = error_counter + 1;
      end
      if (dec_error_syndrome !== 0) begin
        $error("Test %0d FAILED: error syndrome = 0x%0h", i, dec_error_syndrome);
        error_counter = error_counter + 1;
      end

      // Wait for a cycle before next test
      @(negedge clk);
    end

    $display("Testing with single bit error injection.");
    for (i = 0; i < num_tests; i = i + 1) begin
      test_data = $urandom;

      for (int inj_index = 0; inj_index < ChannelWidth; inj_index = inj_index + 1) begin
        // Apply data to encoder at negedge clk
        // TODO: this only works when E2ELatency is 0.
        @(negedge clk);
        data_valid = 1;
        data = test_data;
        #1;
        // Inject single-bit error on the received codeword and send to decoder
        injected = pre_inject;
        injected[inj_index] = !injected[inj_index];
        #1;
        if (!dec_valid) begin
          $error("Test %0d FAILED: no dec_valid", i);
          error_counter = error_counter + 1;
        end
        if (dec_data !== test_data) begin
          $error("Test %0d FAILED: encoded data = 0x%0h, decoded data = 0x%0h", i, test_data,
                 dec_data);
          error_counter = error_counter + 1;
        end
        if (!dec_error_ce) begin
          $error("Test %0d FAILED: error NOT corrected when it was supposed to", i);
          error_counter = error_counter + 1;
        end
        if (dec_error_due) begin
          $error("Test %0d FAILED: error DUE when it was not supposed to", i);
          error_counter = error_counter + 1;
        end
        if (($countones(dec_error_syndrome) % 2) != 1) begin
          $error("Test %0d FAILED: error syndrome = 0x%0h", i, dec_error_syndrome);
          error_counter = error_counter + 1;
        end

        // Wait for a cycle before next test
        @(negedge clk);
      end
    end

    $display("Testing with double bit error injection.");
    for (i = 0; i < num_tests; i = i + 1) begin
      test_data = $urandom;

      for (int i = 0; i < num_double_bit_injections_per_test; i = i + 1) begin
        // Inject double-bit errors on random pairs of locations.
        // (Exhaustive testing is prohibitively expensive for large channels).
        inj_index0 = $urandom % ChannelWidth;
        inj_index1 = $urandom % ChannelWidth;
        while (inj_index0 == inj_index1) begin
          inj_index1 = $urandom % ChannelWidth;
        end

        // Apply data to encoder at negedge clk
        // TODO: this only works when E2ELatency is 0.
        @(negedge clk);
        data_valid = 1;
        data = test_data;
        #1;
        injected = pre_inject;
        injected[inj_index0] = !injected[inj_index0];
        injected[inj_index1] = !injected[inj_index1];
        #1;
        if (!dec_valid) begin
          $error("Test %0d FAILED: no dec_valid", i);
          error_counter = error_counter + 1;
        end
        // Don't sample the decoded data. It might sometimes be correct even with double-bit errors
        // because they could have been injected only in the parity bits (because the code is in
        // systematic form).
        if (dec_error_ce) begin
          $error("Test %0d FAILED: error corrected when it was not supposed to", i);
          error_counter = error_counter + 1;
        end
        if (!dec_error_due) begin
          $error("Test %0d FAILED: error not DUE when it was supposed to", i);
          error_counter = error_counter + 1;
        end
        if (($countones(dec_error_syndrome) % 2) != 0) begin
          $error("Test %0d FAILED: error syndrome = 0x%0h", i, dec_error_syndrome);
          error_counter = error_counter + 1;
        end

        // Wait for a cycle before next test
        @(negedge clk);
      end
    end

    // Print final result
    if (error_counter == 0) begin
      $display("TEST PASSED: All %0d tests passed.", num_tests);
    end else begin
      $error("TEST FAILED: %0d errors found.", error_counter);
    end

    data_valid = 0;
    repeat (10) @(negedge clk);

    $finish;
  end

endmodule
