// Copyright 2024 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
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


// Testbench for br_ecc_secded_encoder and br_ecc_secded_decoder

`timescale 1ns / 1ps

module br_ecc_secded_encoder_decoder_tb;

  // Parameters
  parameter int DataWidth = 8;
  parameter int ParityWidth = 5;
  // Separate RegisterOutputs parameters for encoder and decoder
  parameter bit EncoderRegisterOutputs = 0;
  parameter bit DecoderRegisterOutputs = 0;
  parameter bit DecoderRegisterSyndrome = 0;
  localparam int MessageWidth = 2 ** $clog2(DataWidth);
  localparam int CodewordWidth = MessageWidth + ParityWidth;

  localparam int E2ELatency =
      EncoderRegisterOutputs + DecoderRegisterSyndrome + DecoderRegisterOutputs;

  // Clock and reset
  logic clk;
  logic rst;

  // Encoder inputs
  logic encoder_data_valid;
  logic [DataWidth-1:0] encoder_data;

  // Encoder outputs (directly connected to decoder inputs)
  logic encoder_codeword_valid;
  logic [CodewordWidth-1:0] encoder_codeword;

  // Decoder outputs
  logic decoder_data_valid;
  logic [DataWidth-1:0] decoder_data;
  logic decoder_data_error_corrected;
  logic decoder_data_error_detected_but_uncorrectable;
  logic [ParityWidth-1:0] decoder_data_error_syndrome;

  // Instantiate encoder
  br_ecc_secded_encoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterOutputs(EncoderRegisterOutputs)
  ) br_ecc_secded_encoder (
      .clk,
      .rst,
      .data_valid(encoder_data_valid),
      .data(encoder_data),
      .codeword_valid(encoder_codeword_valid),
      .codeword(encoder_codeword)
  );

  // Instantiate decoder (inputs connected directly to encoder outputs)
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterSyndrome(DecoderRegisterSyndrome),
      .RegisterOutputs(DecoderRegisterOutputs)
  ) br_ecc_secded_decoder (
      .clk,
      .rst,
      .codeword_valid(encoder_codeword_valid),
      .codeword(encoder_codeword),
      .data_valid(decoder_data_valid),
      .data(decoder_data),
      .data_error_corrected(decoder_data_error_corrected),
      .data_error_detected_but_uncorrectable(decoder_data_error_detected_but_uncorrectable),
      .data_error_syndrome(decoder_data_error_syndrome)
  );

  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;  // 100MHz clock

  // Test process
  logic [DataWidth-1:0] test_data;
  int num_tests = 100;
  int i;
  int error_counter = 0;

  initial begin
    rst = 1;
    encoder_data_valid = 0;
    encoder_data = 0;
    repeat (10) @(negedge clk);
    rst = 0;
    repeat (10) @(negedge clk);

    $display("Testing without error injection.");
    for (i = 0; i < num_tests; i = i + 1) begin
      test_data = $urandom;

      // Apply data to encoder at negedge clk
      // TODO: this only works when E2ELatency is 0.
      @(negedge clk);
      encoder_data_valid = 1;
      encoder_data = test_data;
      #1;
      if (!decoder_data_valid) begin
        $error("Test %0d FAILED: no decoder_data_valid", i);
        error_counter = error_counter + 1;
      end
      if (decoder_data !== test_data) begin
        $error("Test %0d FAILED: encoded data = 0x%0h, decoded data = 0x%0h", i, test_data,
               decoder_data);
        error_counter = error_counter + 1;
      end
      if (decoder_data_error_corrected) begin
        $error("Test %0d FAILED: error corrected when it was not supposed to", i);
        error_counter = error_counter + 1;
      end
      if (decoder_data_error_detected_but_uncorrectable) begin
        $error("Test %0d FAILED: error detected_but_uncorrectable when it was not supposed to", i);
        error_counter = error_counter + 1;
      end

      // Wait for a cycle before next test
      @(negedge clk);
    end

    // TODO: Test single error correction and double-error-detection.

    // Print final result
    if (error_counter == 0) begin
      $display("TEST PASSED: All %0d tests passed.", num_tests);
    end else begin
      $error("TEST FAILED: %0d errors found.", error_counter);
    end

    $finish;
  end

endmodule