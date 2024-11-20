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
//     codeword == {parity, msg}
//
// This is a purely combinational module. Valid bits are provided for
// convenience of user integration and port compatibility with the
// corresponding decoder module (br_ecc_sed_decoder).

`include "br_asserts_internal.svh"

module br_ecc_sed_encoder #(
    parameter int MessageWidth = 1,  // Must be at least 1
    localparam int CodewordWidth = MessageWidth + 1
) (
    input  logic                     message_valid,
    input  logic [ MessageWidth-1:0] message,
    output logic                     codeword_valid,
    output logic [CodewordWidth-1:0] codeword
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(message_width_gte_1_a, MessageWidth >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Even parity: the total number of 1s in a valid codeword
  // (including the parity bits) is even.
  logic message_parity;
  assign message_parity = ^message;
  assign codeword = {message_parity, message};
  assign codeword_valid = message_valid;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_COMB_IMPL(codeword_valid_eq_msg_valid_a, codeword_valid == msg_valid)
  `BR_ASSERT_COMB_IMPL(even_parity_a, ^codeword == 1'b0)

endmodule : br_ecc_sed_encoder
