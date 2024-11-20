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

// Bedrock-RTL Single-Error-Detecting (SED - Even Parity) Decoder
//
// Decodes a message using a single-error-detecting linear block code
// in systematic form (in layperson's terms: a simple even parity decoder).
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
// corresponding encoder module (br_ecc_sed_encoder).
//
// The message is still marked valid even if an error is detected.
// The single_error_detected signal is always valid, though it will be 0
// if message_valid is 0.

`include "br_asserts_internal.svh"

module br_ecc_sed_decoder #(
    parameter int MessageWidth = 1,  // Must be at least 1
    localparam int CodewordWidth = MessageWidth + 1
) (
    input  logic                     codeword_valid,
    input  logic [CodewordWidth-1:0] codeword,
    output logic                     message_valid,
    output logic [ MessageWidth-1:0] message,
    output logic                     single_error_detected
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(message_width_gte_1_a, MessageWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // SED code cannot correct errors, so just forward the message portion
  // of the codeword as-is even if an error is detected.
  assign message_valid = codeword_valid;
  assign message = codeword[MessageWidth-1:0];

  // Even parity: the total number of 1s in a valid codeword
  // (including the parity bits) is even.
  logic codeword_parity;
  logic codeword_parity_is_even;
  assign codeword_parity = ^codeword;
  assign codeword_parity_is_even = codeword_parity == 1'b0;

  assign single_error_detected = codeword_valid && !codeword_parity_is_even;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_IMPL(codeword_valid_eq_message_valid_a, codeword_valid == message_valid)

endmodule : br_ecc_sed_decoder
