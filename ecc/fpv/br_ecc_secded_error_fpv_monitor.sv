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

// Bedrock-RTL Single-Error-Correcting, Double-Error-Detecting (SECDED - Hsiao)
// This FV TB focuses on:
//      single error correction
//      double error detection

// Any data width >= 1 is supported. It is internally zero-padded up to
// the nearest power-of-2 message width before being encoded. The following
// table outlines the number of parity bits required for different message widths.

// | Message Width (k) | Parity Width (r) | Codeword Width (n)|
// |-------------------|------------------|-------------------|
// | 4                 | 4                | 8                 |
// | 11                | 5                | 16                |
// | 26                | 6                | 32                |
// | 57                | 7                | 64                |
// | 120               | 8                | 128               |
// | 247               | 9                | 256               |
// | 502               | 10               | 512               |
// | 1013              | 11               | 1024              |
// | 2036              | 12               | 2048              |

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_ecc_secded_error_fpv_monitor #(
    parameter int DataWidth = 4,
    parameter int ParityWidth = 4,
    parameter bit EncRegisterInputs = 0,
    parameter bit EncRegisterOutputs = 0,
    parameter bit DecRegisterInputs = 0,
    parameter bit DecRegisterOutputs = 0,
    parameter bit RegisterSyndrome = 0,
    localparam int InputWidth = DataWidth + ParityWidth,
    localparam int MessageWidth = 2 ** $clog2(DataWidth),
    localparam int CodewordWidth = MessageWidth + ParityWidth
) (
    input logic                 clk,
    input logic                 rst,
    input logic                 data_valid,
    input logic [DataWidth-1:0] data
);

  localparam int EncLatency = EncRegisterInputs + EncRegisterOutputs;
  localparam int DecLatency = DecRegisterInputs + DecRegisterOutputs + RegisterSyndrome;
  localparam int Latency = EncLatency + DecLatency;

  // FV helper signals
  logic [$clog2(InputWidth)-1:0] magic_bit0, magic_bit1;
  // encoder outputs
  logic                     enc_valid;
  logic [    DataWidth-1:0] enc_data;
  logic [  ParityWidth-1:0] enc_parity;
  logic [CodewordWidth-1:0] enc_codeword;
  // decoder inputs
  logic [    DataWidth-1:0] se_rcv_data;
  logic [  ParityWidth-1:0] se_rcv_parity;
  logic [    DataWidth-1:0] de_rcv_data;
  logic [  ParityWidth-1:0] de_rcv_parity;
  // decoder outputs with single error
  logic                     se_dec_valid;
  logic [   InputWidth-1:0] se_dec_codeword;
  logic                     se_dec_error_ce;  // corrected error
  logic                     se_dec_error_due;  // detected-but-uncorrectable error
  logic [  ParityWidth-1:0] se_dec_error_syndrome;
  logic [    DataWidth-1:0] se_dec_data;
  // decoder outputs with double error
  logic                     de_dec_valid;
  logic [   InputWidth-1:0] de_dec_codeword;
  logic                     de_dec_error_ce;  // corrected error
  logic                     de_dec_error_due;  // detected-but-uncorrectable error
  logic [  ParityWidth-1:0] de_dec_error_syndrome;
  logic [    DataWidth-1:0] de_dec_data;
  // FV signals
  logic [   InputWidth-1:0] rcv_codeword;
  logic [   InputWidth-1:0] se_rcv_codeword;
  logic [   InputWidth-1:0] de_rcv_codeword;

  // ----------Instantiate br_ecc_secded_encoder----------
  br_ecc_secded_encoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterInputs(EncRegisterInputs),
      .RegisterOutputs(EncRegisterOutputs)
  ) br_ecc_secded_encoder (
      .clk,
      .rst,
      .data_valid,
      .data,
      .enc_valid,
      .enc_data,
      .enc_parity,
      .enc_codeword
  );

  // ----------Instantiate br_ecc_secded_encoder----------
  // Pass in codeword with single bit flipped
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterInputs(DecRegisterInputs),
      .RegisterSyndrome(RegisterSyndrome),
      .RegisterOutputs(DecRegisterOutputs)
  ) se_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_data(se_rcv_data),
      .rcv_parity(se_rcv_parity),
      .dec_valid(se_dec_valid),
      .dec_codeword(se_dec_codeword),
      .dec_error_ce(se_dec_error_ce),
      .dec_error_due(se_dec_error_due),
      .dec_error_syndrome(se_dec_error_syndrome),
      .dec_data(se_dec_data)
  );

  // Pass in codeword with double bit flipped
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterInputs(DecRegisterInputs),
      .RegisterSyndrome(RegisterSyndrome),
      .RegisterOutputs(DecRegisterOutputs)
  ) de_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_data(de_rcv_data),
      .rcv_parity(de_rcv_parity),
      .dec_valid(de_dec_valid),
      .dec_codeword(de_dec_codeword),
      .dec_error_ce(de_dec_error_ce),
      .dec_error_due(de_dec_error_due),
      .dec_error_syndrome(de_dec_error_syndrome),
      .dec_data(de_dec_data)
  );

  // ----------FV modeling----------
  assign rcv_codeword  = {enc_parity, enc_data};
  assign se_rcv_data   = se_rcv_codeword[DataWidth-1:0];
  assign se_rcv_parity = se_rcv_codeword[InputWidth-1:DataWidth];
  assign de_rcv_data   = de_rcv_codeword[DataWidth-1:0];
  assign de_rcv_parity = de_rcv_codeword[InputWidth-1:DataWidth];

  always_comb begin
    for (int i = 0; i < InputWidth; i++) begin
      se_rcv_codeword[i] = (i == magic_bit0) ? !rcv_codeword[i] : rcv_codeword[i];
      de_rcv_codeword[i] = (i == magic_bit0 || i == magic_bit1) ?
                            !rcv_codeword[i] : rcv_codeword[i];
    end
  end

  // ----------FV assumptions----------
  `BR_FV_2RAND_IDX(magic_bit0, magic_bit1, InputWidth)

  // ----------FV assertions----------
  if (Latency == 0) begin : gen_latency0
    `BR_ASSERT(se_data_integrity_a, se_dec_valid |-> se_dec_data == data)
  end else begin : gen_latency_non0
    `BR_ASSERT(se_data_integrity_a, se_dec_valid |-> se_dec_data == $past(data, Latency))
  end

  `BR_ASSERT(dec_error_ce_a, se_dec_valid |-> se_dec_error_ce && !se_dec_error_due)
  `BR_ASSERT(dec_error_due_a, de_dec_valid |-> !de_dec_error_ce && de_dec_error_due)

endmodule : br_ecc_secded_error_fpv_monitor
