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

// Bedrock-RTL Single-Error-Detecting (SED - Even Parity) Encoder
//
// Encodes a message using a single-error-detecting linear block code
// in systematic form (in layperson's terms: a simple even parity encoder).
//
// Even parity means that the total number of 1s in a valid codeword is even.
// If the codeword has an odd number of 1s, then the decoder will detect it as
// an invalid codeword and report an error.
//
// Systematic form means that the codeword is formed by appending the
// calculated parity bits to the message, i.e., the code has the property
// that the message bits are 1:1 with a slice of bits in the codeword (if they
// have not been corrupted).
//
// In Bedrock ECC libs, our convention is to always append the parity bits on
// the MSbs:
//     codeword == {parity, message}
//
// This is a purely combinational module. Valid bits are provided for
// convenience of user integration and port compatibility with the
// corresponding decoder module (br_ecc_sed_decoder).

`include "br_asserts_internal.svh"

module br_ecc_sed_encoder #(
    parameter int DataWidth = 1,  // Must be at least 1
    // If 1, then insert a pipeline register at the input.
    parameter bit RegisterInputs = 0,
    // If 1, then insert a pipeline register at the output.
    parameter bit RegisterOutputs = 0,
    // Message width is the same as the data width (no internal padding)
    localparam int ParityWidth = 1,
    localparam int CodewordWidth = DataWidth + ParityWidth,
    // ri lint_check_waive PARAM_NOT_USED
    localparam int Latency = RegisterInputs + RegisterOutputs
) (
    // Positive edge-triggered clock.
    input  logic                     clk,
    // Synchronous active-high reset.
    input  logic                     rst,
    input  logic                     data_valid,
    input  logic [    DataWidth-1:0] data,
    output logic                     enc_valid,
    output logic [CodewordWidth-1:0] enc_codeword
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(data_width_gte_1_a, DataWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  //------
  // Optionally register the input signals.
  //------
  logic data_valid_d;
  logic [DataWidth-1:0] data_d;

  br_delay_valid #(
      .Width(DataWidth),
      .NumStages(RegisterInputs == 1 ? 1 : 0)
  ) br_delay_valid_inputs (
      .clk,
      .rst,
      .in_valid(data_valid),
      .in(data),
      .out_valid(data_valid_d),
      .out(data_d),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  // ------
  // Compute parity
  // ------

  // Even parity: the total number of 1s in a valid codeword
  // (including the parity bits) is even.
  logic parity;
  logic [CodewordWidth-1:0] codeword;
  assign parity   = ^data_d;
  assign codeword = {parity, data_d};

  //------
  // Optionally register the output signals.
  //------
  br_delay_valid #(
      .Width(CodewordWidth),
      .NumStages(RegisterOutputs == 1 ? 1 : 0)
  ) br_delay_valid_outputs (
      .clk,
      .rst,
      .in_valid(data_valid_d),
      .in(codeword),
      .out_valid(enc_valid),
      .out(enc_codeword),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(latency_a, data_valid |-> ##Latency enc_valid)
  `BR_ASSERT_IMPL(even_parity_a, enc_valid |-> ^enc_codeword == 1'b0)

endmodule : br_ecc_sed_encoder
