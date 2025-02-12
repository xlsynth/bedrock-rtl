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
//      basic protocols
//      encoder has no encoding error
//      decoer can correctly decode if enc_codeword has no error

// Any data width >= 1 is supported. It is internally zero-padded up to
// the nearest power-of-2 message width before being encoded. The following
// table outlines the number of parity bits required for different message widths.

// | Message Width (k) | Parity Width (r) | Codeword Width (n)|
// |-------------------|------------------|-------------------|
// | 4                 | 4                | 8                 |
// | 8                 | 5                | 13                |
// | 16                | 6                | 22                |
// | 32                | 7                | 39                |
// | 64                | 8                | 72                |
// | 128               | 9                | 137               |
// | 256               | 10               | 266               |
// | 512               | 11               | 523               |
// | 1024              | 12               | 1036              |

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_ecc_secded_fpv_monitor #(
    parameter int DataWidth = 1,
    parameter int ParityWidth = 4,
    parameter bit EncRegisterInputs = 0,
    parameter bit EncRegisterOutputs = 0,
    parameter bit DecRegisterInputs = 0,
    parameter bit DecRegisterOutputs = 0,
    parameter bit RegisterSyndrome = 0,
    localparam int InputWidth = DataWidth + ParityWidth,
    localparam int MessageWidth = 2 ** (ParityWidth - 2),
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
  // encoder outputs
  logic                     enc_valid;
  logic [    DataWidth-1:0] enc_data;
  logic [  ParityWidth-1:0] enc_parity;
  logic [CodewordWidth-1:0] enc_codeword;
  // decoder outputs
  logic                     dec_valid;
  logic [   InputWidth-1:0] dec_codeword;
  logic                     dec_error_ce;  // corrected error
  logic                     dec_error_due;  // detected-but-uncorrectable error
  logic [  ParityWidth-1:0] dec_error_syndrome;
  logic [    DataWidth-1:0] dec_data;

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
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .ParityWidth(ParityWidth),
      .RegisterInputs(DecRegisterInputs),
      .RegisterSyndrome(RegisterSyndrome),
      .RegisterOutputs(DecRegisterOutputs)
  ) br_ecc_secded_decoder (
      .clk,
      .rst,
      .rcv_valid (enc_valid),
      .rcv_data  (enc_data),
      .rcv_parity(enc_parity),
      .dec_valid,
      .dec_codeword,
      .dec_error_ce,
      .dec_error_due,
      .dec_error_syndrome,
      .dec_data
  );

  // Since FPV monitor directly connects encoder and decoder
  // This check doesn't expect ecc error
  // This proves encoder is working
  // This also proves decoder is working if enc_data/parity has no error
  // ----------FV assertions----------
  `BR_ASSERT(no_dec_error_ce_a, dec_valid |-> !dec_error_ce)
  `BR_ASSERT(no_dec_error_due_a, dec_valid |-> !dec_error_due)

  if (Latency == 0) begin : gen_latency0
    `BR_ASSERT(dec_valid_a, data_valid |-> dec_valid)
    `BR_ASSERT(data_integrity_a, dec_valid |-> dec_data == data)
  end else begin : gen_latency_non0
    `BR_ASSERT(dec_valid_a, data_valid |-> ##Latency dec_valid)
    `BR_ASSERT(data_integrity_a, dec_valid |-> dec_data == $past(data, Latency))
  end

endmodule : br_ecc_secded_fpv_monitor
