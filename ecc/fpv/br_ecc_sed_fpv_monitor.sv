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

// Bedrock-RTL Single-Error-Detecting (SED - Even Parity)

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_ecc_sed_fpv_monitor #(
    parameter int DataWidth = 1,
    parameter bit EncRegisterInputs = 0,
    parameter bit EncRegisterOutputs = 0,
    parameter bit DecRegisterInputs = 0,
    parameter bit DecRegisterOutputs = 0,
    localparam int ParityWidth = 1,
    localparam int CodewordWidth = DataWidth + ParityWidth
) (
    input logic                 clk,
    input logic                 rst,
    input logic                 data_valid,
    input logic [DataWidth-1:0] data
);

  localparam int EncLatency = int'(EncRegisterInputs) + int'(EncRegisterOutputs);
  localparam int DecLatency = int'(DecRegisterInputs) + int'(DecRegisterOutputs);
  localparam int Latency = EncLatency + DecLatency;
  // encoder outputs
  logic enc_valid;
  logic [CodewordWidth-1:0] enc_codeword;
  // decoder outputs
  logic dec_valid;
  logic [CodewordWidth-1:0] dec_codeword;
  logic dec_error_due;
  logic dec_error_syndrome;
  logic [DataWidth-1:0] dec_data;

  // ----------Instantiate br_ecc_sed_encoder----------
  br_ecc_sed_encoder #(
      .DataWidth(DataWidth),
      .RegisterInputs(EncRegisterInputs),
      .RegisterOutputs(EncRegisterOutputs)
  ) br_ecc_sed_encoder (
      .clk,
      .rst,
      .data_valid,
      .data,
      .enc_valid,
      .enc_codeword
  );

  // ----------Instantiate br_ecc_sed_encoder----------
  br_ecc_sed_decoder #(
      .DataWidth(DataWidth),
      .RegisterInputs(DecRegisterInputs),
      .RegisterOutputs(DecRegisterOutputs)
  ) br_ecc_sed_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_codeword(enc_codeword),
      .dec_valid,
      .dec_codeword,
      .dec_error_due,
      .dec_error_syndrome,
      .dec_data
  );

  // ----------FV assertions----------
  if (Latency == 0) begin : gen_latency0
    `BR_ASSERT(dec_valid_a, data_valid |-> dec_valid)
    `BR_ASSERT(data_integrity_a, dec_valid && !dec_error_syndrome |-> dec_data == data)
  end else begin : gen_latency_non0
    `BR_ASSERT(dec_valid_a, data_valid |-> ##Latency dec_valid)
    `BR_ASSERT(data_integrity_a,
               dec_valid && !dec_error_syndrome |-> dec_data == $past(data, Latency))
  end

  // if decoder receives codeword with error
  `BR_ASSERT(ecc_error_sanity_a, enc_valid && ^enc_codeword |-> ##DecLatency dec_error_syndrome)
  `BR_ASSERT(ecc_error_a, dec_valid && dec_error_syndrome |-> dec_error_due)

endmodule : br_ecc_sed_fpv_monitor
