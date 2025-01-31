// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// Copyright 2024-2025 The Bedrock-RTL Authors
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
  parameter bit EncoderRegisterInputs = 0;
  parameter bit EncoderRegisterOutputs = 0;
  parameter bit DecoderRegisterInputs = 0;
  parameter bit DecoderRegisterSyndrome = 0;
  parameter bit DecoderRegisterOutputs = 0;
  localparam int MessageWidth = 2 ** $clog2(DataWidth);
  localparam int CodewordWidth = MessageWidth + ParityWidth;

  localparam int E2ELatency =
      EncoderRegisterInputs +
      EncoderRegisterOutputs +
      DecoderRegisterInputs +
      DecoderRegisterSyndrome +
      DecoderRegisterOutputs;

  // Clock and reset
  logic clk;
  logic rst;

  // Encoder inputs
  logic data_valid;
  logic [DataWidth-1:0] data;

  // Encoder outputs (directly connected to decoder inputs)
  logic enc_valid;
  logic [DataWidth-1:0] enc_data;
  logic [ParityWidth-1:0] enc_parity;

  // Decoder outputs
  logic dec_valid;
  logic [DataWidth-1:0] dec_data;
  logic dec_error_ce;
  logic dec_error_due;
  logic [ParityWidth-1:0] dec_error_syndrome;

  // Instantiate encoder
  br_ecc_secded_encoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
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

  // Instantiate decoder (inputs connected directly to encoder outputs)
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterInputs(DecoderRegisterInputs),
      .RegisterSyndrome(DecoderRegisterSyndrome),
      .RegisterOutputs(DecoderRegisterOutputs)
  ) br_ecc_secded_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_data(enc_data),
      .rcv_parity(enc_parity),
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
  int num_tests = 100;
  int i;
  int error_counter = 0;

  initial begin
    rst = 1;
    data_valid = 0;
    data = 0;
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
