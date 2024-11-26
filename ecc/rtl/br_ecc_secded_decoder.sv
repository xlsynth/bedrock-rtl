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


// verilog_format: off
// verilog_lint: waive-start line-length

// Bedrock-RTL Single-Error-Correcting, Double-Error-Detecting (SECDED - Hsiao) Decoder
//
// Decodes a codeword using a single-error-correcting, double-error-detecting
// linear block code in systematic form (in layperson's terms: a Hsiao SECDED [1] decoder,
// closely related to Hamming codes).
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
// The data is still marked valid even if an error is detected.
//
// This module has a parameterizable number of pipeline stages, ranging from fully
// combinational to 2 cycles of latency.
//
// Any data width >= 1 is supported. It is considered internally zero-padded up to
// the nearest power-of-2 message width as part of decoding. The following
// table outlines the number of parity bits required for different message widths.
//
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
//
// The number of parity bits must be one of the values in the table above
// or the module will not elaborate.
//
// References:
// [1] https://ieeexplore.ieee.org/abstract/document/5391627

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_unused.svh"

// TODO(mgottscho): Pipeline the syndrome decoding and then correction with a parameter.
module br_ecc_secded_decoder #(
    parameter int DataWidth = 1,  // Must be at least 1
    parameter int ParityWidth = 4,  // Must be at least 4 and at most 12
    // If 1, then insert a pipeline register between syndrome computation and
    // syndrome decoding (error correction).
    parameter bit RegisterSyndrome = 0,
    // If 1, then insert a pipeline register at the output.
    parameter bit RegisterOutputs = 0,
    localparam int MessageWidth = 2 ** $clog2(DataWidth),
    localparam int CodewordWidth = MessageWidth + ParityWidth
) (
    // Positive edge-triggered clock.
    input  logic                     clk,
    // Synchronous active-high reset.
    input  logic                     rst,
    input  logic                     codeword_valid,
    input  logic [CodewordWidth-1:0] codeword,
    output logic                     data_valid,
    output logic [    DataWidth-1:0] data,
    output logic                     data_error_corrected,
    output logic                     data_error_detected_but_uncorrectable,
    output logic [  ParityWidth-1:0] data_error_syndrome
);

  // ri lint_check_waive PARAM_NOT_USED
  localparam int Latency = RegisterSyndrome + RegisterOutputs;

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(message_width_gte_1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(parity_width_gte_4_a, ParityWidth >= 4)
  `BR_ASSERT_STATIC(parity_width_lte_12_a, ParityWidth <= 12)
  `BR_ASSERT_STATIC(message_width_is_power_of_2_a, br_math::is_power_of_2(MessageWidth))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic [CodewordWidth-1:0][ParityWidth-1:0] parity_check_matrix;  // H
  logic [ParityWidth-1:0] syndrome;

  //------
  // Compute syndrome and set up constant parity check matrix.
  //------

  // ri lint_check_off EXPR_ID_LIMIT

  if ((CodewordWidth == 4) && (MessageWidth == 4)) begin : gen_8_4
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 4)
    assign syndrome[0] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[4];
    assign syndrome[1] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5];
    assign syndrome[2] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[6];
    assign syndrome[3] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[7];
    assign parity_check_matrix[0] = 4'b0111;
    assign parity_check_matrix[1] = 4'b1011;
    assign parity_check_matrix[2] = 4'b1101;
    assign parity_check_matrix[3] = 4'b1110;
    assign parity_check_matrix[4] = 4'b1000;
    assign parity_check_matrix[5] = 4'b0100;
    assign parity_check_matrix[6] = 4'b0010;
    assign parity_check_matrix[7] = 4'b0001;
  end else if ((CodewordWidth == 13) && (MessageWidth == 8)) begin : gen_13_8
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 5)
    assign syndrome[0] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8];
    assign syndrome[1] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[9];
    assign syndrome[2] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[10];
    assign syndrome[3] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[11];
    assign syndrome[4] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[12];
    assign parity_check_matrix[0] = 5'b00111;
    assign parity_check_matrix[1] = 5'b01011;
    assign parity_check_matrix[2] = 5'b01101;
    assign parity_check_matrix[3] = 5'b01110;
    assign parity_check_matrix[4] = 5'b10011;
    assign parity_check_matrix[5] = 5'b10101;
    assign parity_check_matrix[6] = 5'b10110;
    assign parity_check_matrix[7] = 5'b11001;
    assign parity_check_matrix[8] = 5'b10000;
    assign parity_check_matrix[9] = 5'b01000;
    assign parity_check_matrix[10] = 5'b00100;
    assign parity_check_matrix[11] = 5'b00010;
    assign parity_check_matrix[12] = 5'b00001;
  end else if ((CodewordWidth == 22) && (MessageWidth == 16)) begin : gen_22_16
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 6)
    assign syndrome[0] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16];
    assign syndrome[1] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[17];
    assign syndrome[2] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[18];
    assign syndrome[3] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[19];
    assign syndrome[4] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[20];
    assign syndrome[5] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[21];
    assign parity_check_matrix[0] = 6'b000111;
    assign parity_check_matrix[1] = 6'b001011;
    assign parity_check_matrix[2] = 6'b001101;
    assign parity_check_matrix[3] = 6'b001110;
    assign parity_check_matrix[4] = 6'b010011;
    assign parity_check_matrix[5] = 6'b010101;
    assign parity_check_matrix[6] = 6'b010110;
    assign parity_check_matrix[7] = 6'b011001;
    assign parity_check_matrix[8] = 6'b011010;
    assign parity_check_matrix[9] = 6'b011100;
    assign parity_check_matrix[10] = 6'b100011;
    assign parity_check_matrix[11] = 6'b100101;
    assign parity_check_matrix[12] = 6'b100110;
    assign parity_check_matrix[13] = 6'b101001;
    assign parity_check_matrix[14] = 6'b101010;
    assign parity_check_matrix[15] = 6'b101100;
    assign parity_check_matrix[16] = 6'b100000;
    assign parity_check_matrix[17] = 6'b010000;
    assign parity_check_matrix[18] = 6'b001000;
    assign parity_check_matrix[19] = 6'b000100;
    assign parity_check_matrix[20] = 6'b000010;
    assign parity_check_matrix[21] = 6'b000001;
  end else if ((CodewordWidth == 39) && (MessageWidth == 32)) begin : gen_39_32
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 7)
    assign syndrome[0] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32];
    assign syndrome[1] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[33];
    assign syndrome[2] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34];
    assign syndrome[3] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[35];
    assign syndrome[4] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[36];
    assign syndrome[5] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[37];
    assign syndrome[6] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[38];
    assign parity_check_matrix[0] = 7'b0000111;
    assign parity_check_matrix[1] = 7'b0001011;
    assign parity_check_matrix[2] = 7'b0001101;
    assign parity_check_matrix[3] = 7'b0001110;
    assign parity_check_matrix[4] = 7'b0010011;
    assign parity_check_matrix[5] = 7'b0010101;
    assign parity_check_matrix[6] = 7'b0010110;
    assign parity_check_matrix[7] = 7'b0011001;
    assign parity_check_matrix[8] = 7'b0011010;
    assign parity_check_matrix[9] = 7'b0011100;
    assign parity_check_matrix[10] = 7'b0100011;
    assign parity_check_matrix[11] = 7'b0100101;
    assign parity_check_matrix[12] = 7'b0100110;
    assign parity_check_matrix[13] = 7'b0101001;
    assign parity_check_matrix[14] = 7'b0101010;
    assign parity_check_matrix[15] = 7'b0101100;
    assign parity_check_matrix[16] = 7'b0110001;
    assign parity_check_matrix[17] = 7'b0110010;
    assign parity_check_matrix[18] = 7'b0110100;
    assign parity_check_matrix[19] = 7'b0111000;
    assign parity_check_matrix[20] = 7'b1000011;
    assign parity_check_matrix[21] = 7'b1000101;
    assign parity_check_matrix[22] = 7'b1000110;
    assign parity_check_matrix[23] = 7'b1001001;
    assign parity_check_matrix[24] = 7'b1001010;
    assign parity_check_matrix[25] = 7'b1001100;
    assign parity_check_matrix[26] = 7'b1010001;
    assign parity_check_matrix[27] = 7'b1010010;
    assign parity_check_matrix[28] = 7'b1010100;
    assign parity_check_matrix[29] = 7'b1011000;
    assign parity_check_matrix[30] = 7'b1100001;
    assign parity_check_matrix[31] = 7'b1100010;
    assign parity_check_matrix[32] = 7'b1000000;
    assign parity_check_matrix[33] = 7'b0100000;
    assign parity_check_matrix[34] = 7'b0010000;
    assign parity_check_matrix[35] = 7'b0001000;
    assign parity_check_matrix[36] = 7'b0000100;
    assign parity_check_matrix[37] = 7'b0000010;
    assign parity_check_matrix[38] = 7'b0000001;
  end else if ((CodewordWidth == 72) && (MessageWidth == 64)) begin : gen_72_64
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 8)
    assign syndrome[0] = codeword[35] ^ codeword[36] ^ codeword[37] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[64];
    assign syndrome[1] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[62] ^ codeword[63] ^ codeword[65];
    assign syndrome[2] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[55] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[66];
    assign syndrome[3] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[49] ^ codeword[54] ^ codeword[56] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[63] ^ codeword[67];
    assign syndrome[4] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[33] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[44] ^ codeword[48] ^ codeword[53] ^ codeword[56] ^ codeword[57] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[68];
    assign syndrome[5] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[32] ^ codeword[36] ^ codeword[37] ^ codeword[40] ^ codeword[43] ^ codeword[47] ^ codeword[52] ^ codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[69];
    assign syndrome[6] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[35] ^ codeword[37] ^ codeword[39] ^ codeword[42] ^ codeword[46] ^ codeword[51] ^ codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[70];
    assign syndrome[7] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[35] ^ codeword[36] ^ codeword[38] ^ codeword[41] ^ codeword[45] ^ codeword[50] ^ codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[62] ^ codeword[63] ^ codeword[71];
    assign parity_check_matrix[0] = 8'b00000111;
    assign parity_check_matrix[1] = 8'b00001011;
    assign parity_check_matrix[2] = 8'b00001101;
    assign parity_check_matrix[3] = 8'b00001110;
    assign parity_check_matrix[4] = 8'b00010011;
    assign parity_check_matrix[5] = 8'b00010101;
    assign parity_check_matrix[6] = 8'b00010110;
    assign parity_check_matrix[7] = 8'b00011001;
    assign parity_check_matrix[8] = 8'b00011010;
    assign parity_check_matrix[9] = 8'b00011100;
    assign parity_check_matrix[10] = 8'b00100011;
    assign parity_check_matrix[11] = 8'b00100101;
    assign parity_check_matrix[12] = 8'b00100110;
    assign parity_check_matrix[13] = 8'b00101001;
    assign parity_check_matrix[14] = 8'b00101010;
    assign parity_check_matrix[15] = 8'b00101100;
    assign parity_check_matrix[16] = 8'b00110001;
    assign parity_check_matrix[17] = 8'b00110010;
    assign parity_check_matrix[18] = 8'b00110100;
    assign parity_check_matrix[19] = 8'b00111000;
    assign parity_check_matrix[20] = 8'b01000011;
    assign parity_check_matrix[21] = 8'b01000101;
    assign parity_check_matrix[22] = 8'b01000110;
    assign parity_check_matrix[23] = 8'b01001001;
    assign parity_check_matrix[24] = 8'b01001010;
    assign parity_check_matrix[25] = 8'b01001100;
    assign parity_check_matrix[26] = 8'b01010001;
    assign parity_check_matrix[27] = 8'b01010010;
    assign parity_check_matrix[28] = 8'b01010100;
    assign parity_check_matrix[29] = 8'b01011000;
    assign parity_check_matrix[30] = 8'b01100001;
    assign parity_check_matrix[31] = 8'b01100010;
    assign parity_check_matrix[32] = 8'b01100100;
    assign parity_check_matrix[33] = 8'b01101000;
    assign parity_check_matrix[34] = 8'b01110000;
    assign parity_check_matrix[35] = 8'b10000011;
    assign parity_check_matrix[36] = 8'b10000101;
    assign parity_check_matrix[37] = 8'b10000110;
    assign parity_check_matrix[38] = 8'b10001001;
    assign parity_check_matrix[39] = 8'b10001010;
    assign parity_check_matrix[40] = 8'b10001100;
    assign parity_check_matrix[41] = 8'b10010001;
    assign parity_check_matrix[42] = 8'b10010010;
    assign parity_check_matrix[43] = 8'b10010100;
    assign parity_check_matrix[44] = 8'b10011000;
    assign parity_check_matrix[45] = 8'b10100001;
    assign parity_check_matrix[46] = 8'b10100010;
    assign parity_check_matrix[47] = 8'b10100100;
    assign parity_check_matrix[48] = 8'b10101000;
    assign parity_check_matrix[49] = 8'b10110000;
    assign parity_check_matrix[50] = 8'b11000001;
    assign parity_check_matrix[51] = 8'b11000010;
    assign parity_check_matrix[52] = 8'b11000100;
    assign parity_check_matrix[53] = 8'b11001000;
    assign parity_check_matrix[54] = 8'b11010000;
    assign parity_check_matrix[55] = 8'b11100000;
    assign parity_check_matrix[56] = 8'b00011111;
    assign parity_check_matrix[57] = 8'b00101111;
    assign parity_check_matrix[58] = 8'b00110111;
    assign parity_check_matrix[59] = 8'b00111011;
    assign parity_check_matrix[60] = 8'b00111101;
    assign parity_check_matrix[61] = 8'b00111110;
    assign parity_check_matrix[62] = 8'b01001111;
    assign parity_check_matrix[63] = 8'b01010111;
    assign parity_check_matrix[64] = 8'b10000000;
    assign parity_check_matrix[65] = 8'b01000000;
    assign parity_check_matrix[66] = 8'b00100000;
    assign parity_check_matrix[67] = 8'b00010000;
    assign parity_check_matrix[68] = 8'b00001000;
    assign parity_check_matrix[69] = 8'b00000100;
    assign parity_check_matrix[70] = 8'b00000010;
    assign parity_check_matrix[71] = 8'b00000001;
  end else if ((CodewordWidth == 137) && (MessageWidth == 128)) begin : gen_137_128
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 9)
    assign syndrome[0] = codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[128];
    assign syndrome[1] = codeword[35] ^ codeword[36] ^ codeword[37] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[129];
    assign syndrome[2] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[83] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[130];
    assign syndrome[3] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[55] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[76] ^ codeword[82] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[131];
    assign syndrome[4] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[49] ^ codeword[54] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[70] ^ codeword[75] ^ codeword[81] ^ codeword[84] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[132];
    assign syndrome[5] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[33] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[44] ^ codeword[48] ^ codeword[53] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[65] ^ codeword[69] ^ codeword[74] ^ codeword[80] ^ codeword[84] ^ codeword[85] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[90] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[105] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[127] ^ codeword[133];
    assign syndrome[6] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[32] ^ codeword[36] ^ codeword[37] ^ codeword[40] ^ codeword[43] ^ codeword[47] ^ codeword[52] ^ codeword[57] ^ codeword[58] ^ codeword[61] ^ codeword[64] ^ codeword[68] ^ codeword[73] ^ codeword[79] ^ codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[88] ^ codeword[89] ^ codeword[90] ^ codeword[91] ^ codeword[93] ^ codeword[94] ^ codeword[95] ^ codeword[97] ^ codeword[98] ^ codeword[100] ^ codeword[101] ^ codeword[104] ^ codeword[105] ^ codeword[106] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[112] ^ codeword[113] ^ codeword[115] ^ codeword[116] ^ codeword[119] ^ codeword[120] ^ codeword[122] ^ codeword[123] ^ codeword[125] ^ codeword[126] ^ codeword[134];
    assign syndrome[7] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[35] ^ codeword[37] ^ codeword[39] ^ codeword[42] ^ codeword[46] ^ codeword[51] ^ codeword[56] ^ codeword[58] ^ codeword[60] ^ codeword[63] ^ codeword[67] ^ codeword[72] ^ codeword[78] ^ codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[89] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[98] ^ codeword[99] ^ codeword[101] ^ codeword[103] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[113] ^ codeword[114] ^ codeword[116] ^ codeword[118] ^ codeword[120] ^ codeword[121] ^ codeword[123] ^ codeword[124] ^ codeword[126] ^ codeword[135];
    assign syndrome[8] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[35] ^ codeword[36] ^ codeword[38] ^ codeword[41] ^ codeword[45] ^ codeword[50] ^ codeword[56] ^ codeword[57] ^ codeword[59] ^ codeword[62] ^ codeword[66] ^ codeword[71] ^ codeword[77] ^ codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[99] ^ codeword[100] ^ codeword[102] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[114] ^ codeword[115] ^ codeword[117] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[124] ^ codeword[125] ^ codeword[127] ^ codeword[136];
    assign parity_check_matrix[0] = 9'b000000111;
    assign parity_check_matrix[1] = 9'b000001011;
    assign parity_check_matrix[2] = 9'b000001101;
    assign parity_check_matrix[3] = 9'b000001110;
    assign parity_check_matrix[4] = 9'b000010011;
    assign parity_check_matrix[5] = 9'b000010101;
    assign parity_check_matrix[6] = 9'b000010110;
    assign parity_check_matrix[7] = 9'b000011001;
    assign parity_check_matrix[8] = 9'b000011010;
    assign parity_check_matrix[9] = 9'b000011100;
    assign parity_check_matrix[10] = 9'b000100011;
    assign parity_check_matrix[11] = 9'b000100101;
    assign parity_check_matrix[12] = 9'b000100110;
    assign parity_check_matrix[13] = 9'b000101001;
    assign parity_check_matrix[14] = 9'b000101010;
    assign parity_check_matrix[15] = 9'b000101100;
    assign parity_check_matrix[16] = 9'b000110001;
    assign parity_check_matrix[17] = 9'b000110010;
    assign parity_check_matrix[18] = 9'b000110100;
    assign parity_check_matrix[19] = 9'b000111000;
    assign parity_check_matrix[20] = 9'b001000011;
    assign parity_check_matrix[21] = 9'b001000101;
    assign parity_check_matrix[22] = 9'b001000110;
    assign parity_check_matrix[23] = 9'b001001001;
    assign parity_check_matrix[24] = 9'b001001010;
    assign parity_check_matrix[25] = 9'b001001100;
    assign parity_check_matrix[26] = 9'b001010001;
    assign parity_check_matrix[27] = 9'b001010010;
    assign parity_check_matrix[28] = 9'b001010100;
    assign parity_check_matrix[29] = 9'b001011000;
    assign parity_check_matrix[30] = 9'b001100001;
    assign parity_check_matrix[31] = 9'b001100010;
    assign parity_check_matrix[32] = 9'b001100100;
    assign parity_check_matrix[33] = 9'b001101000;
    assign parity_check_matrix[34] = 9'b001110000;
    assign parity_check_matrix[35] = 9'b010000011;
    assign parity_check_matrix[36] = 9'b010000101;
    assign parity_check_matrix[37] = 9'b010000110;
    assign parity_check_matrix[38] = 9'b010001001;
    assign parity_check_matrix[39] = 9'b010001010;
    assign parity_check_matrix[40] = 9'b010001100;
    assign parity_check_matrix[41] = 9'b010010001;
    assign parity_check_matrix[42] = 9'b010010010;
    assign parity_check_matrix[43] = 9'b010010100;
    assign parity_check_matrix[44] = 9'b010011000;
    assign parity_check_matrix[45] = 9'b010100001;
    assign parity_check_matrix[46] = 9'b010100010;
    assign parity_check_matrix[47] = 9'b010100100;
    assign parity_check_matrix[48] = 9'b010101000;
    assign parity_check_matrix[49] = 9'b010110000;
    assign parity_check_matrix[50] = 9'b011000001;
    assign parity_check_matrix[51] = 9'b011000010;
    assign parity_check_matrix[52] = 9'b011000100;
    assign parity_check_matrix[53] = 9'b011001000;
    assign parity_check_matrix[54] = 9'b011010000;
    assign parity_check_matrix[55] = 9'b011100000;
    assign parity_check_matrix[56] = 9'b100000011;
    assign parity_check_matrix[57] = 9'b100000101;
    assign parity_check_matrix[58] = 9'b100000110;
    assign parity_check_matrix[59] = 9'b100001001;
    assign parity_check_matrix[60] = 9'b100001010;
    assign parity_check_matrix[61] = 9'b100001100;
    assign parity_check_matrix[62] = 9'b100010001;
    assign parity_check_matrix[63] = 9'b100010010;
    assign parity_check_matrix[64] = 9'b100010100;
    assign parity_check_matrix[65] = 9'b100011000;
    assign parity_check_matrix[66] = 9'b100100001;
    assign parity_check_matrix[67] = 9'b100100010;
    assign parity_check_matrix[68] = 9'b100100100;
    assign parity_check_matrix[69] = 9'b100101000;
    assign parity_check_matrix[70] = 9'b100110000;
    assign parity_check_matrix[71] = 9'b101000001;
    assign parity_check_matrix[72] = 9'b101000010;
    assign parity_check_matrix[73] = 9'b101000100;
    assign parity_check_matrix[74] = 9'b101001000;
    assign parity_check_matrix[75] = 9'b101010000;
    assign parity_check_matrix[76] = 9'b101100000;
    assign parity_check_matrix[77] = 9'b110000001;
    assign parity_check_matrix[78] = 9'b110000010;
    assign parity_check_matrix[79] = 9'b110000100;
    assign parity_check_matrix[80] = 9'b110001000;
    assign parity_check_matrix[81] = 9'b110010000;
    assign parity_check_matrix[82] = 9'b110100000;
    assign parity_check_matrix[83] = 9'b111000000;
    assign parity_check_matrix[84] = 9'b000011111;
    assign parity_check_matrix[85] = 9'b000101111;
    assign parity_check_matrix[86] = 9'b000110111;
    assign parity_check_matrix[87] = 9'b000111011;
    assign parity_check_matrix[88] = 9'b000111101;
    assign parity_check_matrix[89] = 9'b000111110;
    assign parity_check_matrix[90] = 9'b001001111;
    assign parity_check_matrix[91] = 9'b001010111;
    assign parity_check_matrix[92] = 9'b001011011;
    assign parity_check_matrix[93] = 9'b001011101;
    assign parity_check_matrix[94] = 9'b001011110;
    assign parity_check_matrix[95] = 9'b001100111;
    assign parity_check_matrix[96] = 9'b001101011;
    assign parity_check_matrix[97] = 9'b001101101;
    assign parity_check_matrix[98] = 9'b001101110;
    assign parity_check_matrix[99] = 9'b001110011;
    assign parity_check_matrix[100] = 9'b001110101;
    assign parity_check_matrix[101] = 9'b001110110;
    assign parity_check_matrix[102] = 9'b001111001;
    assign parity_check_matrix[103] = 9'b001111010;
    assign parity_check_matrix[104] = 9'b001111100;
    assign parity_check_matrix[105] = 9'b010001111;
    assign parity_check_matrix[106] = 9'b010010111;
    assign parity_check_matrix[107] = 9'b010011011;
    assign parity_check_matrix[108] = 9'b010011101;
    assign parity_check_matrix[109] = 9'b010011110;
    assign parity_check_matrix[110] = 9'b010100111;
    assign parity_check_matrix[111] = 9'b010101011;
    assign parity_check_matrix[112] = 9'b010101101;
    assign parity_check_matrix[113] = 9'b010101110;
    assign parity_check_matrix[114] = 9'b010110011;
    assign parity_check_matrix[115] = 9'b010110101;
    assign parity_check_matrix[116] = 9'b010110110;
    assign parity_check_matrix[117] = 9'b010111001;
    assign parity_check_matrix[118] = 9'b010111010;
    assign parity_check_matrix[119] = 9'b010111100;
    assign parity_check_matrix[120] = 9'b011000111;
    assign parity_check_matrix[121] = 9'b011001011;
    assign parity_check_matrix[122] = 9'b011001101;
    assign parity_check_matrix[123] = 9'b011001110;
    assign parity_check_matrix[124] = 9'b011010011;
    assign parity_check_matrix[125] = 9'b011010101;
    assign parity_check_matrix[126] = 9'b011010110;
    assign parity_check_matrix[127] = 9'b011011001;
    assign parity_check_matrix[128] = 9'b100000000;
    assign parity_check_matrix[129] = 9'b010000000;
    assign parity_check_matrix[130] = 9'b001000000;
    assign parity_check_matrix[131] = 9'b000100000;
    assign parity_check_matrix[132] = 9'b000010000;
    assign parity_check_matrix[133] = 9'b000001000;
    assign parity_check_matrix[134] = 9'b000000100;
    assign parity_check_matrix[135] = 9'b000000010;
    assign parity_check_matrix[136] = 9'b000000001;
  end else if ((CodewordWidth == 266) && (MessageWidth == 256)) begin : gen_266_256
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 10)
    assign syndrome[0] = codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[256];
    assign syndrome[1] = codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[257];
    assign syndrome[2] = codeword[35] ^ codeword[36] ^ codeword[37] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[119] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[258];
    assign syndrome[3] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[83] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[111] ^ codeword[118] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[259];
    assign syndrome[4] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[55] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[76] ^ codeword[82] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[104] ^ codeword[110] ^ codeword[117] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[146] ^ codeword[147] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[260];
    assign syndrome[5] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[49] ^ codeword[54] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[70] ^ codeword[75] ^ codeword[81] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[98] ^ codeword[103] ^ codeword[109] ^ codeword[116] ^ codeword[120] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[130] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[165] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[185] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[245] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[255] ^ codeword[261];
    assign syndrome[6] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[33] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[44] ^ codeword[48] ^ codeword[53] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[65] ^ codeword[69] ^ codeword[74] ^ codeword[80] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[93] ^ codeword[97] ^ codeword[102] ^ codeword[108] ^ codeword[115] ^ codeword[120] ^ codeword[121] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[128] ^ codeword[129] ^ codeword[130] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[141] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[147] ^ codeword[148] ^ codeword[149] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[163] ^ codeword[164] ^ codeword[165] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[175] ^ codeword[176] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[210] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[230] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[240] ^ codeword[244] ^ codeword[246] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[262];
    assign syndrome[7] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[32] ^ codeword[36] ^ codeword[37] ^ codeword[40] ^ codeword[43] ^ codeword[47] ^ codeword[52] ^ codeword[57] ^ codeword[58] ^ codeword[61] ^ codeword[64] ^ codeword[68] ^ codeword[73] ^ codeword[79] ^ codeword[85] ^ codeword[86] ^ codeword[89] ^ codeword[92] ^ codeword[96] ^ codeword[101] ^ codeword[107] ^ codeword[114] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[129] ^ codeword[130] ^ codeword[131] ^ codeword[133] ^ codeword[134] ^ codeword[136] ^ codeword[137] ^ codeword[140] ^ codeword[141] ^ codeword[142] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[148] ^ codeword[149] ^ codeword[151] ^ codeword[152] ^ codeword[155] ^ codeword[156] ^ codeword[158] ^ codeword[159] ^ codeword[161] ^ codeword[162] ^ codeword[165] ^ codeword[167] ^ codeword[168] ^ codeword[171] ^ codeword[174] ^ codeword[176] ^ codeword[177] ^ codeword[179] ^ codeword[180] ^ codeword[181] ^ codeword[183] ^ codeword[184] ^ codeword[186] ^ codeword[187] ^ codeword[190] ^ codeword[191] ^ codeword[193] ^ codeword[194] ^ codeword[196] ^ codeword[197] ^ codeword[200] ^ codeword[202] ^ codeword[203] ^ codeword[206] ^ codeword[209] ^ codeword[211] ^ codeword[213] ^ codeword[214] ^ codeword[216] ^ codeword[217] ^ codeword[220] ^ codeword[222] ^ codeword[223] ^ codeword[226] ^ codeword[229] ^ codeword[232] ^ codeword[233] ^ codeword[236] ^ codeword[239] ^ codeword[243] ^ codeword[246] ^ codeword[247] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[253] ^ codeword[254] ^ codeword[263];
    assign syndrome[8] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[35] ^ codeword[37] ^ codeword[39] ^ codeword[42] ^ codeword[46] ^ codeword[51] ^ codeword[56] ^ codeword[58] ^ codeword[60] ^ codeword[63] ^ codeword[67] ^ codeword[72] ^ codeword[78] ^ codeword[84] ^ codeword[86] ^ codeword[88] ^ codeword[91] ^ codeword[95] ^ codeword[100] ^ codeword[106] ^ codeword[113] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[134] ^ codeword[135] ^ codeword[137] ^ codeword[139] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[149] ^ codeword[150] ^ codeword[152] ^ codeword[154] ^ codeword[156] ^ codeword[157] ^ codeword[159] ^ codeword[160] ^ codeword[162] ^ codeword[164] ^ codeword[166] ^ codeword[168] ^ codeword[170] ^ codeword[173] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[184] ^ codeword[185] ^ codeword[187] ^ codeword[189] ^ codeword[191] ^ codeword[192] ^ codeword[194] ^ codeword[195] ^ codeword[197] ^ codeword[199] ^ codeword[201] ^ codeword[203] ^ codeword[205] ^ codeword[208] ^ codeword[211] ^ codeword[212] ^ codeword[214] ^ codeword[215] ^ codeword[217] ^ codeword[219] ^ codeword[221] ^ codeword[223] ^ codeword[225] ^ codeword[228] ^ codeword[231] ^ codeword[233] ^ codeword[235] ^ codeword[238] ^ codeword[242] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[254] ^ codeword[255] ^ codeword[264];
    assign syndrome[9] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[35] ^ codeword[36] ^ codeword[38] ^ codeword[41] ^ codeword[45] ^ codeword[50] ^ codeword[56] ^ codeword[57] ^ codeword[59] ^ codeword[62] ^ codeword[66] ^ codeword[71] ^ codeword[77] ^ codeword[84] ^ codeword[85] ^ codeword[87] ^ codeword[90] ^ codeword[94] ^ codeword[99] ^ codeword[105] ^ codeword[112] ^ codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[135] ^ codeword[136] ^ codeword[138] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[146] ^ codeword[147] ^ codeword[148] ^ codeword[150] ^ codeword[151] ^ codeword[153] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[160] ^ codeword[161] ^ codeword[163] ^ codeword[166] ^ codeword[167] ^ codeword[169] ^ codeword[172] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[185] ^ codeword[186] ^ codeword[188] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[195] ^ codeword[196] ^ codeword[198] ^ codeword[201] ^ codeword[202] ^ codeword[204] ^ codeword[207] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[215] ^ codeword[216] ^ codeword[218] ^ codeword[221] ^ codeword[222] ^ codeword[224] ^ codeword[227] ^ codeword[231] ^ codeword[232] ^ codeword[234] ^ codeword[237] ^ codeword[241] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[255] ^ codeword[265];
    assign parity_check_matrix[0] = 10'b0000000111;
    assign parity_check_matrix[1] = 10'b0000001011;
    assign parity_check_matrix[2] = 10'b0000001101;
    assign parity_check_matrix[3] = 10'b0000001110;
    assign parity_check_matrix[4] = 10'b0000010011;
    assign parity_check_matrix[5] = 10'b0000010101;
    assign parity_check_matrix[6] = 10'b0000010110;
    assign parity_check_matrix[7] = 10'b0000011001;
    assign parity_check_matrix[8] = 10'b0000011010;
    assign parity_check_matrix[9] = 10'b0000011100;
    assign parity_check_matrix[10] = 10'b0000100011;
    assign parity_check_matrix[11] = 10'b0000100101;
    assign parity_check_matrix[12] = 10'b0000100110;
    assign parity_check_matrix[13] = 10'b0000101001;
    assign parity_check_matrix[14] = 10'b0000101010;
    assign parity_check_matrix[15] = 10'b0000101100;
    assign parity_check_matrix[16] = 10'b0000110001;
    assign parity_check_matrix[17] = 10'b0000110010;
    assign parity_check_matrix[18] = 10'b0000110100;
    assign parity_check_matrix[19] = 10'b0000111000;
    assign parity_check_matrix[20] = 10'b0001000011;
    assign parity_check_matrix[21] = 10'b0001000101;
    assign parity_check_matrix[22] = 10'b0001000110;
    assign parity_check_matrix[23] = 10'b0001001001;
    assign parity_check_matrix[24] = 10'b0001001010;
    assign parity_check_matrix[25] = 10'b0001001100;
    assign parity_check_matrix[26] = 10'b0001010001;
    assign parity_check_matrix[27] = 10'b0001010010;
    assign parity_check_matrix[28] = 10'b0001010100;
    assign parity_check_matrix[29] = 10'b0001011000;
    assign parity_check_matrix[30] = 10'b0001100001;
    assign parity_check_matrix[31] = 10'b0001100010;
    assign parity_check_matrix[32] = 10'b0001100100;
    assign parity_check_matrix[33] = 10'b0001101000;
    assign parity_check_matrix[34] = 10'b0001110000;
    assign parity_check_matrix[35] = 10'b0010000011;
    assign parity_check_matrix[36] = 10'b0010000101;
    assign parity_check_matrix[37] = 10'b0010000110;
    assign parity_check_matrix[38] = 10'b0010001001;
    assign parity_check_matrix[39] = 10'b0010001010;
    assign parity_check_matrix[40] = 10'b0010001100;
    assign parity_check_matrix[41] = 10'b0010010001;
    assign parity_check_matrix[42] = 10'b0010010010;
    assign parity_check_matrix[43] = 10'b0010010100;
    assign parity_check_matrix[44] = 10'b0010011000;
    assign parity_check_matrix[45] = 10'b0010100001;
    assign parity_check_matrix[46] = 10'b0010100010;
    assign parity_check_matrix[47] = 10'b0010100100;
    assign parity_check_matrix[48] = 10'b0010101000;
    assign parity_check_matrix[49] = 10'b0010110000;
    assign parity_check_matrix[50] = 10'b0011000001;
    assign parity_check_matrix[51] = 10'b0011000010;
    assign parity_check_matrix[52] = 10'b0011000100;
    assign parity_check_matrix[53] = 10'b0011001000;
    assign parity_check_matrix[54] = 10'b0011010000;
    assign parity_check_matrix[55] = 10'b0011100000;
    assign parity_check_matrix[56] = 10'b0100000011;
    assign parity_check_matrix[57] = 10'b0100000101;
    assign parity_check_matrix[58] = 10'b0100000110;
    assign parity_check_matrix[59] = 10'b0100001001;
    assign parity_check_matrix[60] = 10'b0100001010;
    assign parity_check_matrix[61] = 10'b0100001100;
    assign parity_check_matrix[62] = 10'b0100010001;
    assign parity_check_matrix[63] = 10'b0100010010;
    assign parity_check_matrix[64] = 10'b0100010100;
    assign parity_check_matrix[65] = 10'b0100011000;
    assign parity_check_matrix[66] = 10'b0100100001;
    assign parity_check_matrix[67] = 10'b0100100010;
    assign parity_check_matrix[68] = 10'b0100100100;
    assign parity_check_matrix[69] = 10'b0100101000;
    assign parity_check_matrix[70] = 10'b0100110000;
    assign parity_check_matrix[71] = 10'b0101000001;
    assign parity_check_matrix[72] = 10'b0101000010;
    assign parity_check_matrix[73] = 10'b0101000100;
    assign parity_check_matrix[74] = 10'b0101001000;
    assign parity_check_matrix[75] = 10'b0101010000;
    assign parity_check_matrix[76] = 10'b0101100000;
    assign parity_check_matrix[77] = 10'b0110000001;
    assign parity_check_matrix[78] = 10'b0110000010;
    assign parity_check_matrix[79] = 10'b0110000100;
    assign parity_check_matrix[80] = 10'b0110001000;
    assign parity_check_matrix[81] = 10'b0110010000;
    assign parity_check_matrix[82] = 10'b0110100000;
    assign parity_check_matrix[83] = 10'b0111000000;
    assign parity_check_matrix[84] = 10'b1000000011;
    assign parity_check_matrix[85] = 10'b1000000101;
    assign parity_check_matrix[86] = 10'b1000000110;
    assign parity_check_matrix[87] = 10'b1000001001;
    assign parity_check_matrix[88] = 10'b1000001010;
    assign parity_check_matrix[89] = 10'b1000001100;
    assign parity_check_matrix[90] = 10'b1000010001;
    assign parity_check_matrix[91] = 10'b1000010010;
    assign parity_check_matrix[92] = 10'b1000010100;
    assign parity_check_matrix[93] = 10'b1000011000;
    assign parity_check_matrix[94] = 10'b1000100001;
    assign parity_check_matrix[95] = 10'b1000100010;
    assign parity_check_matrix[96] = 10'b1000100100;
    assign parity_check_matrix[97] = 10'b1000101000;
    assign parity_check_matrix[98] = 10'b1000110000;
    assign parity_check_matrix[99] = 10'b1001000001;
    assign parity_check_matrix[100] = 10'b1001000010;
    assign parity_check_matrix[101] = 10'b1001000100;
    assign parity_check_matrix[102] = 10'b1001001000;
    assign parity_check_matrix[103] = 10'b1001010000;
    assign parity_check_matrix[104] = 10'b1001100000;
    assign parity_check_matrix[105] = 10'b1010000001;
    assign parity_check_matrix[106] = 10'b1010000010;
    assign parity_check_matrix[107] = 10'b1010000100;
    assign parity_check_matrix[108] = 10'b1010001000;
    assign parity_check_matrix[109] = 10'b1010010000;
    assign parity_check_matrix[110] = 10'b1010100000;
    assign parity_check_matrix[111] = 10'b1011000000;
    assign parity_check_matrix[112] = 10'b1100000001;
    assign parity_check_matrix[113] = 10'b1100000010;
    assign parity_check_matrix[114] = 10'b1100000100;
    assign parity_check_matrix[115] = 10'b1100001000;
    assign parity_check_matrix[116] = 10'b1100010000;
    assign parity_check_matrix[117] = 10'b1100100000;
    assign parity_check_matrix[118] = 10'b1101000000;
    assign parity_check_matrix[119] = 10'b1110000000;
    assign parity_check_matrix[120] = 10'b0000011111;
    assign parity_check_matrix[121] = 10'b0000101111;
    assign parity_check_matrix[122] = 10'b0000110111;
    assign parity_check_matrix[123] = 10'b0000111011;
    assign parity_check_matrix[124] = 10'b0000111101;
    assign parity_check_matrix[125] = 10'b0000111110;
    assign parity_check_matrix[126] = 10'b0001001111;
    assign parity_check_matrix[127] = 10'b0001010111;
    assign parity_check_matrix[128] = 10'b0001011011;
    assign parity_check_matrix[129] = 10'b0001011101;
    assign parity_check_matrix[130] = 10'b0001011110;
    assign parity_check_matrix[131] = 10'b0001100111;
    assign parity_check_matrix[132] = 10'b0001101011;
    assign parity_check_matrix[133] = 10'b0001101101;
    assign parity_check_matrix[134] = 10'b0001101110;
    assign parity_check_matrix[135] = 10'b0001110011;
    assign parity_check_matrix[136] = 10'b0001110101;
    assign parity_check_matrix[137] = 10'b0001110110;
    assign parity_check_matrix[138] = 10'b0001111001;
    assign parity_check_matrix[139] = 10'b0001111010;
    assign parity_check_matrix[140] = 10'b0001111100;
    assign parity_check_matrix[141] = 10'b0010001111;
    assign parity_check_matrix[142] = 10'b0010010111;
    assign parity_check_matrix[143] = 10'b0010011011;
    assign parity_check_matrix[144] = 10'b0010011101;
    assign parity_check_matrix[145] = 10'b0010011110;
    assign parity_check_matrix[146] = 10'b0010100111;
    assign parity_check_matrix[147] = 10'b0010101011;
    assign parity_check_matrix[148] = 10'b0010101101;
    assign parity_check_matrix[149] = 10'b0010101110;
    assign parity_check_matrix[150] = 10'b0010110011;
    assign parity_check_matrix[151] = 10'b0010110101;
    assign parity_check_matrix[152] = 10'b0010110110;
    assign parity_check_matrix[153] = 10'b0010111001;
    assign parity_check_matrix[154] = 10'b0010111010;
    assign parity_check_matrix[155] = 10'b0010111100;
    assign parity_check_matrix[156] = 10'b0011000111;
    assign parity_check_matrix[157] = 10'b0011001011;
    assign parity_check_matrix[158] = 10'b0011001101;
    assign parity_check_matrix[159] = 10'b0011001110;
    assign parity_check_matrix[160] = 10'b0011010011;
    assign parity_check_matrix[161] = 10'b0011010101;
    assign parity_check_matrix[162] = 10'b0011010110;
    assign parity_check_matrix[163] = 10'b0011011001;
    assign parity_check_matrix[164] = 10'b0011011010;
    assign parity_check_matrix[165] = 10'b0011011100;
    assign parity_check_matrix[166] = 10'b0011100011;
    assign parity_check_matrix[167] = 10'b0011100101;
    assign parity_check_matrix[168] = 10'b0011100110;
    assign parity_check_matrix[169] = 10'b0011101001;
    assign parity_check_matrix[170] = 10'b0011101010;
    assign parity_check_matrix[171] = 10'b0011101100;
    assign parity_check_matrix[172] = 10'b0011110001;
    assign parity_check_matrix[173] = 10'b0011110010;
    assign parity_check_matrix[174] = 10'b0011110100;
    assign parity_check_matrix[175] = 10'b0011111000;
    assign parity_check_matrix[176] = 10'b0100001111;
    assign parity_check_matrix[177] = 10'b0100010111;
    assign parity_check_matrix[178] = 10'b0100011011;
    assign parity_check_matrix[179] = 10'b0100011101;
    assign parity_check_matrix[180] = 10'b0100011110;
    assign parity_check_matrix[181] = 10'b0100100111;
    assign parity_check_matrix[182] = 10'b0100101011;
    assign parity_check_matrix[183] = 10'b0100101101;
    assign parity_check_matrix[184] = 10'b0100101110;
    assign parity_check_matrix[185] = 10'b0100110011;
    assign parity_check_matrix[186] = 10'b0100110101;
    assign parity_check_matrix[187] = 10'b0100110110;
    assign parity_check_matrix[188] = 10'b0100111001;
    assign parity_check_matrix[189] = 10'b0100111010;
    assign parity_check_matrix[190] = 10'b0100111100;
    assign parity_check_matrix[191] = 10'b0101000111;
    assign parity_check_matrix[192] = 10'b0101001011;
    assign parity_check_matrix[193] = 10'b0101001101;
    assign parity_check_matrix[194] = 10'b0101001110;
    assign parity_check_matrix[195] = 10'b0101010011;
    assign parity_check_matrix[196] = 10'b0101010101;
    assign parity_check_matrix[197] = 10'b0101010110;
    assign parity_check_matrix[198] = 10'b0101011001;
    assign parity_check_matrix[199] = 10'b0101011010;
    assign parity_check_matrix[200] = 10'b0101011100;
    assign parity_check_matrix[201] = 10'b0101100011;
    assign parity_check_matrix[202] = 10'b0101100101;
    assign parity_check_matrix[203] = 10'b0101100110;
    assign parity_check_matrix[204] = 10'b0101101001;
    assign parity_check_matrix[205] = 10'b0101101010;
    assign parity_check_matrix[206] = 10'b0101101100;
    assign parity_check_matrix[207] = 10'b0101110001;
    assign parity_check_matrix[208] = 10'b0101110010;
    assign parity_check_matrix[209] = 10'b0101110100;
    assign parity_check_matrix[210] = 10'b0101111000;
    assign parity_check_matrix[211] = 10'b0110000111;
    assign parity_check_matrix[212] = 10'b0110001011;
    assign parity_check_matrix[213] = 10'b0110001101;
    assign parity_check_matrix[214] = 10'b0110001110;
    assign parity_check_matrix[215] = 10'b0110010011;
    assign parity_check_matrix[216] = 10'b0110010101;
    assign parity_check_matrix[217] = 10'b0110010110;
    assign parity_check_matrix[218] = 10'b0110011001;
    assign parity_check_matrix[219] = 10'b0110011010;
    assign parity_check_matrix[220] = 10'b0110011100;
    assign parity_check_matrix[221] = 10'b0110100011;
    assign parity_check_matrix[222] = 10'b0110100101;
    assign parity_check_matrix[223] = 10'b0110100110;
    assign parity_check_matrix[224] = 10'b0110101001;
    assign parity_check_matrix[225] = 10'b0110101010;
    assign parity_check_matrix[226] = 10'b0110101100;
    assign parity_check_matrix[227] = 10'b0110110001;
    assign parity_check_matrix[228] = 10'b0110110010;
    assign parity_check_matrix[229] = 10'b0110110100;
    assign parity_check_matrix[230] = 10'b0110111000;
    assign parity_check_matrix[231] = 10'b0111000011;
    assign parity_check_matrix[232] = 10'b0111000101;
    assign parity_check_matrix[233] = 10'b0111000110;
    assign parity_check_matrix[234] = 10'b0111001001;
    assign parity_check_matrix[235] = 10'b0111001010;
    assign parity_check_matrix[236] = 10'b0111001100;
    assign parity_check_matrix[237] = 10'b0111010001;
    assign parity_check_matrix[238] = 10'b0111010010;
    assign parity_check_matrix[239] = 10'b0111010100;
    assign parity_check_matrix[240] = 10'b0111011000;
    assign parity_check_matrix[241] = 10'b0111100001;
    assign parity_check_matrix[242] = 10'b0111100010;
    assign parity_check_matrix[243] = 10'b0111100100;
    assign parity_check_matrix[244] = 10'b0111101000;
    assign parity_check_matrix[245] = 10'b0111110000;
    assign parity_check_matrix[246] = 10'b1000001111;
    assign parity_check_matrix[247] = 10'b1000010111;
    assign parity_check_matrix[248] = 10'b1000011011;
    assign parity_check_matrix[249] = 10'b1000011101;
    assign parity_check_matrix[250] = 10'b1000011110;
    assign parity_check_matrix[251] = 10'b1000100111;
    assign parity_check_matrix[252] = 10'b1000101011;
    assign parity_check_matrix[253] = 10'b1000101101;
    assign parity_check_matrix[254] = 10'b1000101110;
    assign parity_check_matrix[255] = 10'b1000110011;
    assign parity_check_matrix[256] = 10'b1000000000;
    assign parity_check_matrix[257] = 10'b0100000000;
    assign parity_check_matrix[258] = 10'b0010000000;
    assign parity_check_matrix[259] = 10'b0001000000;
    assign parity_check_matrix[260] = 10'b0000100000;
    assign parity_check_matrix[261] = 10'b0000010000;
    assign parity_check_matrix[262] = 10'b0000001000;
    assign parity_check_matrix[263] = 10'b0000000100;
    assign parity_check_matrix[264] = 10'b0000000010;
    assign parity_check_matrix[265] = 10'b0000000001;
  end else if ((CodewordWidth == 523) && (MessageWidth == 512)) begin : gen_523_512
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 11)
    assign syndrome[0] = codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[420] ^ codeword[421] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[511] ^ codeword[512];
    assign syndrome[1] = codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[295] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[416] ^ codeword[513];
    assign syndrome[2] = codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[164] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[416] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[511] ^ codeword[514];
    assign syndrome[3] = codeword[35] ^ codeword[36] ^ codeword[37] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[119] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[155] ^ codeword[163] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[416] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[515];
    assign syndrome[4] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[83] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[111] ^ codeword[118] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[147] ^ codeword[154] ^ codeword[162] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[416] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[511] ^ codeword[516];
    assign syndrome[5] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[55] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[76] ^ codeword[82] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[104] ^ codeword[110] ^ codeword[117] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[140] ^ codeword[146] ^ codeword[153] ^ codeword[161] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[416] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[517];
    assign syndrome[6] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[49] ^ codeword[54] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[70] ^ codeword[75] ^ codeword[81] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[98] ^ codeword[103] ^ codeword[109] ^ codeword[116] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[134] ^ codeword[139] ^ codeword[145] ^ codeword[152] ^ codeword[160] ^ codeword[165] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[220] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[290] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[295] ^ codeword[300] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[310] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[330] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[360] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[395] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[410] ^ codeword[415] ^ codeword[418] ^ codeword[419] ^ codeword[420] ^ codeword[421] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[486] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[518];
    assign syndrome[7] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[33] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[44] ^ codeword[48] ^ codeword[53] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[65] ^ codeword[69] ^ codeword[74] ^ codeword[80] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[93] ^ codeword[97] ^ codeword[102] ^ codeword[108] ^ codeword[115] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[129] ^ codeword[133] ^ codeword[138] ^ codeword[144] ^ codeword[151] ^ codeword[159] ^ codeword[165] ^ codeword[166] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[186] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[220] ^ codeword[221] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[255] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[275] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[285] ^ codeword[289] ^ codeword[291] ^ codeword[293] ^ codeword[294] ^ codeword[295] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[325] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[345] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[355] ^ codeword[359] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[380] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[390] ^ codeword[394] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[405] ^ codeword[409] ^ codeword[414] ^ codeword[417] ^ codeword[419] ^ codeword[420] ^ codeword[421] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[451] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[471] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[481] ^ codeword[485] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[506] ^ codeword[510] ^ codeword[511] ^ codeword[519];
    assign syndrome[8] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[32] ^ codeword[36] ^ codeword[37] ^ codeword[40] ^ codeword[43] ^ codeword[47] ^ codeword[52] ^ codeword[57] ^ codeword[58] ^ codeword[61] ^ codeword[64] ^ codeword[68] ^ codeword[73] ^ codeword[79] ^ codeword[85] ^ codeword[86] ^ codeword[89] ^ codeword[92] ^ codeword[96] ^ codeword[101] ^ codeword[107] ^ codeword[114] ^ codeword[121] ^ codeword[122] ^ codeword[125] ^ codeword[128] ^ codeword[132] ^ codeword[137] ^ codeword[143] ^ codeword[150] ^ codeword[158] ^ codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[174] ^ codeword[175] ^ codeword[176] ^ codeword[178] ^ codeword[179] ^ codeword[181] ^ codeword[182] ^ codeword[185] ^ codeword[186] ^ codeword[187] ^ codeword[189] ^ codeword[190] ^ codeword[191] ^ codeword[193] ^ codeword[194] ^ codeword[196] ^ codeword[197] ^ codeword[200] ^ codeword[201] ^ codeword[203] ^ codeword[204] ^ codeword[206] ^ codeword[207] ^ codeword[210] ^ codeword[212] ^ codeword[213] ^ codeword[216] ^ codeword[219] ^ codeword[221] ^ codeword[222] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[228] ^ codeword[229] ^ codeword[231] ^ codeword[232] ^ codeword[235] ^ codeword[236] ^ codeword[238] ^ codeword[239] ^ codeword[241] ^ codeword[242] ^ codeword[245] ^ codeword[247] ^ codeword[248] ^ codeword[251] ^ codeword[254] ^ codeword[256] ^ codeword[258] ^ codeword[259] ^ codeword[261] ^ codeword[262] ^ codeword[265] ^ codeword[267] ^ codeword[268] ^ codeword[271] ^ codeword[274] ^ codeword[277] ^ codeword[278] ^ codeword[281] ^ codeword[284] ^ codeword[288] ^ codeword[291] ^ codeword[292] ^ codeword[294] ^ codeword[295] ^ codeword[296] ^ codeword[298] ^ codeword[299] ^ codeword[301] ^ codeword[302] ^ codeword[305] ^ codeword[306] ^ codeword[308] ^ codeword[309] ^ codeword[311] ^ codeword[312] ^ codeword[315] ^ codeword[317] ^ codeword[318] ^ codeword[321] ^ codeword[324] ^ codeword[326] ^ codeword[328] ^ codeword[329] ^ codeword[331] ^ codeword[332] ^ codeword[335] ^ codeword[337] ^ codeword[338] ^ codeword[341] ^ codeword[344] ^ codeword[347] ^ codeword[348] ^ codeword[351] ^ codeword[354] ^ codeword[358] ^ codeword[361] ^ codeword[363] ^ codeword[364] ^ codeword[366] ^ codeword[367] ^ codeword[370] ^ codeword[372] ^ codeword[373] ^ codeword[376] ^ codeword[379] ^ codeword[382] ^ codeword[383] ^ codeword[386] ^ codeword[389] ^ codeword[393] ^ codeword[397] ^ codeword[398] ^ codeword[401] ^ codeword[404] ^ codeword[408] ^ codeword[413] ^ codeword[417] ^ codeword[418] ^ codeword[420] ^ codeword[421] ^ codeword[422] ^ codeword[424] ^ codeword[425] ^ codeword[427] ^ codeword[428] ^ codeword[431] ^ codeword[432] ^ codeword[434] ^ codeword[435] ^ codeword[437] ^ codeword[438] ^ codeword[441] ^ codeword[443] ^ codeword[444] ^ codeword[447] ^ codeword[450] ^ codeword[452] ^ codeword[454] ^ codeword[455] ^ codeword[457] ^ codeword[458] ^ codeword[461] ^ codeword[463] ^ codeword[464] ^ codeword[467] ^ codeword[470] ^ codeword[473] ^ codeword[474] ^ codeword[477] ^ codeword[480] ^ codeword[484] ^ codeword[487] ^ codeword[489] ^ codeword[490] ^ codeword[492] ^ codeword[493] ^ codeword[496] ^ codeword[498] ^ codeword[499] ^ codeword[502] ^ codeword[505] ^ codeword[508] ^ codeword[509] ^ codeword[520];
    assign syndrome[9] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[35] ^ codeword[37] ^ codeword[39] ^ codeword[42] ^ codeword[46] ^ codeword[51] ^ codeword[56] ^ codeword[58] ^ codeword[60] ^ codeword[63] ^ codeword[67] ^ codeword[72] ^ codeword[78] ^ codeword[84] ^ codeword[86] ^ codeword[88] ^ codeword[91] ^ codeword[95] ^ codeword[100] ^ codeword[106] ^ codeword[113] ^ codeword[120] ^ codeword[122] ^ codeword[124] ^ codeword[127] ^ codeword[131] ^ codeword[136] ^ codeword[142] ^ codeword[149] ^ codeword[157] ^ codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[175] ^ codeword[176] ^ codeword[177] ^ codeword[179] ^ codeword[180] ^ codeword[182] ^ codeword[184] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[190] ^ codeword[191] ^ codeword[192] ^ codeword[194] ^ codeword[195] ^ codeword[197] ^ codeword[199] ^ codeword[201] ^ codeword[202] ^ codeword[204] ^ codeword[205] ^ codeword[207] ^ codeword[209] ^ codeword[211] ^ codeword[213] ^ codeword[215] ^ codeword[218] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[229] ^ codeword[230] ^ codeword[232] ^ codeword[234] ^ codeword[236] ^ codeword[237] ^ codeword[239] ^ codeword[240] ^ codeword[242] ^ codeword[244] ^ codeword[246] ^ codeword[248] ^ codeword[250] ^ codeword[253] ^ codeword[256] ^ codeword[257] ^ codeword[259] ^ codeword[260] ^ codeword[262] ^ codeword[264] ^ codeword[266] ^ codeword[268] ^ codeword[270] ^ codeword[273] ^ codeword[276] ^ codeword[278] ^ codeword[280] ^ codeword[283] ^ codeword[287] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[295] ^ codeword[296] ^ codeword[297] ^ codeword[299] ^ codeword[300] ^ codeword[302] ^ codeword[304] ^ codeword[306] ^ codeword[307] ^ codeword[309] ^ codeword[310] ^ codeword[312] ^ codeword[314] ^ codeword[316] ^ codeword[318] ^ codeword[320] ^ codeword[323] ^ codeword[326] ^ codeword[327] ^ codeword[329] ^ codeword[330] ^ codeword[332] ^ codeword[334] ^ codeword[336] ^ codeword[338] ^ codeword[340] ^ codeword[343] ^ codeword[346] ^ codeword[348] ^ codeword[350] ^ codeword[353] ^ codeword[357] ^ codeword[361] ^ codeword[362] ^ codeword[364] ^ codeword[365] ^ codeword[367] ^ codeword[369] ^ codeword[371] ^ codeword[373] ^ codeword[375] ^ codeword[378] ^ codeword[381] ^ codeword[383] ^ codeword[385] ^ codeword[388] ^ codeword[392] ^ codeword[396] ^ codeword[398] ^ codeword[400] ^ codeword[403] ^ codeword[407] ^ codeword[412] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[421] ^ codeword[422] ^ codeword[423] ^ codeword[425] ^ codeword[426] ^ codeword[428] ^ codeword[430] ^ codeword[432] ^ codeword[433] ^ codeword[435] ^ codeword[436] ^ codeword[438] ^ codeword[440] ^ codeword[442] ^ codeword[444] ^ codeword[446] ^ codeword[449] ^ codeword[452] ^ codeword[453] ^ codeword[455] ^ codeword[456] ^ codeword[458] ^ codeword[460] ^ codeword[462] ^ codeword[464] ^ codeword[466] ^ codeword[469] ^ codeword[472] ^ codeword[474] ^ codeword[476] ^ codeword[479] ^ codeword[483] ^ codeword[487] ^ codeword[488] ^ codeword[490] ^ codeword[491] ^ codeword[493] ^ codeword[495] ^ codeword[497] ^ codeword[499] ^ codeword[501] ^ codeword[504] ^ codeword[507] ^ codeword[509] ^ codeword[511] ^ codeword[521];
    assign syndrome[10] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[35] ^ codeword[36] ^ codeword[38] ^ codeword[41] ^ codeword[45] ^ codeword[50] ^ codeword[56] ^ codeword[57] ^ codeword[59] ^ codeword[62] ^ codeword[66] ^ codeword[71] ^ codeword[77] ^ codeword[84] ^ codeword[85] ^ codeword[87] ^ codeword[90] ^ codeword[94] ^ codeword[99] ^ codeword[105] ^ codeword[112] ^ codeword[120] ^ codeword[121] ^ codeword[123] ^ codeword[126] ^ codeword[130] ^ codeword[135] ^ codeword[141] ^ codeword[148] ^ codeword[156] ^ codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[180] ^ codeword[181] ^ codeword[183] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[195] ^ codeword[196] ^ codeword[198] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[205] ^ codeword[206] ^ codeword[208] ^ codeword[211] ^ codeword[212] ^ codeword[214] ^ codeword[217] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[230] ^ codeword[231] ^ codeword[233] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[240] ^ codeword[241] ^ codeword[243] ^ codeword[246] ^ codeword[247] ^ codeword[249] ^ codeword[252] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[260] ^ codeword[261] ^ codeword[263] ^ codeword[266] ^ codeword[267] ^ codeword[269] ^ codeword[272] ^ codeword[276] ^ codeword[277] ^ codeword[279] ^ codeword[282] ^ codeword[286] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[300] ^ codeword[301] ^ codeword[303] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[310] ^ codeword[311] ^ codeword[313] ^ codeword[316] ^ codeword[317] ^ codeword[319] ^ codeword[322] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[330] ^ codeword[331] ^ codeword[333] ^ codeword[336] ^ codeword[337] ^ codeword[339] ^ codeword[342] ^ codeword[346] ^ codeword[347] ^ codeword[349] ^ codeword[352] ^ codeword[356] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[365] ^ codeword[366] ^ codeword[368] ^ codeword[371] ^ codeword[372] ^ codeword[374] ^ codeword[377] ^ codeword[381] ^ codeword[382] ^ codeword[384] ^ codeword[387] ^ codeword[391] ^ codeword[396] ^ codeword[397] ^ codeword[399] ^ codeword[402] ^ codeword[406] ^ codeword[411] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[420] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[426] ^ codeword[427] ^ codeword[429] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[436] ^ codeword[437] ^ codeword[439] ^ codeword[442] ^ codeword[443] ^ codeword[445] ^ codeword[448] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[456] ^ codeword[457] ^ codeword[459] ^ codeword[462] ^ codeword[463] ^ codeword[465] ^ codeword[468] ^ codeword[472] ^ codeword[473] ^ codeword[475] ^ codeword[478] ^ codeword[482] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[491] ^ codeword[492] ^ codeword[494] ^ codeword[497] ^ codeword[498] ^ codeword[500] ^ codeword[503] ^ codeword[507] ^ codeword[508] ^ codeword[510] ^ codeword[522];
    assign parity_check_matrix[0] = 11'b00000000111;
    assign parity_check_matrix[1] = 11'b00000001011;
    assign parity_check_matrix[2] = 11'b00000001101;
    assign parity_check_matrix[3] = 11'b00000001110;
    assign parity_check_matrix[4] = 11'b00000010011;
    assign parity_check_matrix[5] = 11'b00000010101;
    assign parity_check_matrix[6] = 11'b00000010110;
    assign parity_check_matrix[7] = 11'b00000011001;
    assign parity_check_matrix[8] = 11'b00000011010;
    assign parity_check_matrix[9] = 11'b00000011100;
    assign parity_check_matrix[10] = 11'b00000100011;
    assign parity_check_matrix[11] = 11'b00000100101;
    assign parity_check_matrix[12] = 11'b00000100110;
    assign parity_check_matrix[13] = 11'b00000101001;
    assign parity_check_matrix[14] = 11'b00000101010;
    assign parity_check_matrix[15] = 11'b00000101100;
    assign parity_check_matrix[16] = 11'b00000110001;
    assign parity_check_matrix[17] = 11'b00000110010;
    assign parity_check_matrix[18] = 11'b00000110100;
    assign parity_check_matrix[19] = 11'b00000111000;
    assign parity_check_matrix[20] = 11'b00001000011;
    assign parity_check_matrix[21] = 11'b00001000101;
    assign parity_check_matrix[22] = 11'b00001000110;
    assign parity_check_matrix[23] = 11'b00001001001;
    assign parity_check_matrix[24] = 11'b00001001010;
    assign parity_check_matrix[25] = 11'b00001001100;
    assign parity_check_matrix[26] = 11'b00001010001;
    assign parity_check_matrix[27] = 11'b00001010010;
    assign parity_check_matrix[28] = 11'b00001010100;
    assign parity_check_matrix[29] = 11'b00001011000;
    assign parity_check_matrix[30] = 11'b00001100001;
    assign parity_check_matrix[31] = 11'b00001100010;
    assign parity_check_matrix[32] = 11'b00001100100;
    assign parity_check_matrix[33] = 11'b00001101000;
    assign parity_check_matrix[34] = 11'b00001110000;
    assign parity_check_matrix[35] = 11'b00010000011;
    assign parity_check_matrix[36] = 11'b00010000101;
    assign parity_check_matrix[37] = 11'b00010000110;
    assign parity_check_matrix[38] = 11'b00010001001;
    assign parity_check_matrix[39] = 11'b00010001010;
    assign parity_check_matrix[40] = 11'b00010001100;
    assign parity_check_matrix[41] = 11'b00010010001;
    assign parity_check_matrix[42] = 11'b00010010010;
    assign parity_check_matrix[43] = 11'b00010010100;
    assign parity_check_matrix[44] = 11'b00010011000;
    assign parity_check_matrix[45] = 11'b00010100001;
    assign parity_check_matrix[46] = 11'b00010100010;
    assign parity_check_matrix[47] = 11'b00010100100;
    assign parity_check_matrix[48] = 11'b00010101000;
    assign parity_check_matrix[49] = 11'b00010110000;
    assign parity_check_matrix[50] = 11'b00011000001;
    assign parity_check_matrix[51] = 11'b00011000010;
    assign parity_check_matrix[52] = 11'b00011000100;
    assign parity_check_matrix[53] = 11'b00011001000;
    assign parity_check_matrix[54] = 11'b00011010000;
    assign parity_check_matrix[55] = 11'b00011100000;
    assign parity_check_matrix[56] = 11'b00100000011;
    assign parity_check_matrix[57] = 11'b00100000101;
    assign parity_check_matrix[58] = 11'b00100000110;
    assign parity_check_matrix[59] = 11'b00100001001;
    assign parity_check_matrix[60] = 11'b00100001010;
    assign parity_check_matrix[61] = 11'b00100001100;
    assign parity_check_matrix[62] = 11'b00100010001;
    assign parity_check_matrix[63] = 11'b00100010010;
    assign parity_check_matrix[64] = 11'b00100010100;
    assign parity_check_matrix[65] = 11'b00100011000;
    assign parity_check_matrix[66] = 11'b00100100001;
    assign parity_check_matrix[67] = 11'b00100100010;
    assign parity_check_matrix[68] = 11'b00100100100;
    assign parity_check_matrix[69] = 11'b00100101000;
    assign parity_check_matrix[70] = 11'b00100110000;
    assign parity_check_matrix[71] = 11'b00101000001;
    assign parity_check_matrix[72] = 11'b00101000010;
    assign parity_check_matrix[73] = 11'b00101000100;
    assign parity_check_matrix[74] = 11'b00101001000;
    assign parity_check_matrix[75] = 11'b00101010000;
    assign parity_check_matrix[76] = 11'b00101100000;
    assign parity_check_matrix[77] = 11'b00110000001;
    assign parity_check_matrix[78] = 11'b00110000010;
    assign parity_check_matrix[79] = 11'b00110000100;
    assign parity_check_matrix[80] = 11'b00110001000;
    assign parity_check_matrix[81] = 11'b00110010000;
    assign parity_check_matrix[82] = 11'b00110100000;
    assign parity_check_matrix[83] = 11'b00111000000;
    assign parity_check_matrix[84] = 11'b01000000011;
    assign parity_check_matrix[85] = 11'b01000000101;
    assign parity_check_matrix[86] = 11'b01000000110;
    assign parity_check_matrix[87] = 11'b01000001001;
    assign parity_check_matrix[88] = 11'b01000001010;
    assign parity_check_matrix[89] = 11'b01000001100;
    assign parity_check_matrix[90] = 11'b01000010001;
    assign parity_check_matrix[91] = 11'b01000010010;
    assign parity_check_matrix[92] = 11'b01000010100;
    assign parity_check_matrix[93] = 11'b01000011000;
    assign parity_check_matrix[94] = 11'b01000100001;
    assign parity_check_matrix[95] = 11'b01000100010;
    assign parity_check_matrix[96] = 11'b01000100100;
    assign parity_check_matrix[97] = 11'b01000101000;
    assign parity_check_matrix[98] = 11'b01000110000;
    assign parity_check_matrix[99] = 11'b01001000001;
    assign parity_check_matrix[100] = 11'b01001000010;
    assign parity_check_matrix[101] = 11'b01001000100;
    assign parity_check_matrix[102] = 11'b01001001000;
    assign parity_check_matrix[103] = 11'b01001010000;
    assign parity_check_matrix[104] = 11'b01001100000;
    assign parity_check_matrix[105] = 11'b01010000001;
    assign parity_check_matrix[106] = 11'b01010000010;
    assign parity_check_matrix[107] = 11'b01010000100;
    assign parity_check_matrix[108] = 11'b01010001000;
    assign parity_check_matrix[109] = 11'b01010010000;
    assign parity_check_matrix[110] = 11'b01010100000;
    assign parity_check_matrix[111] = 11'b01011000000;
    assign parity_check_matrix[112] = 11'b01100000001;
    assign parity_check_matrix[113] = 11'b01100000010;
    assign parity_check_matrix[114] = 11'b01100000100;
    assign parity_check_matrix[115] = 11'b01100001000;
    assign parity_check_matrix[116] = 11'b01100010000;
    assign parity_check_matrix[117] = 11'b01100100000;
    assign parity_check_matrix[118] = 11'b01101000000;
    assign parity_check_matrix[119] = 11'b01110000000;
    assign parity_check_matrix[120] = 11'b10000000011;
    assign parity_check_matrix[121] = 11'b10000000101;
    assign parity_check_matrix[122] = 11'b10000000110;
    assign parity_check_matrix[123] = 11'b10000001001;
    assign parity_check_matrix[124] = 11'b10000001010;
    assign parity_check_matrix[125] = 11'b10000001100;
    assign parity_check_matrix[126] = 11'b10000010001;
    assign parity_check_matrix[127] = 11'b10000010010;
    assign parity_check_matrix[128] = 11'b10000010100;
    assign parity_check_matrix[129] = 11'b10000011000;
    assign parity_check_matrix[130] = 11'b10000100001;
    assign parity_check_matrix[131] = 11'b10000100010;
    assign parity_check_matrix[132] = 11'b10000100100;
    assign parity_check_matrix[133] = 11'b10000101000;
    assign parity_check_matrix[134] = 11'b10000110000;
    assign parity_check_matrix[135] = 11'b10001000001;
    assign parity_check_matrix[136] = 11'b10001000010;
    assign parity_check_matrix[137] = 11'b10001000100;
    assign parity_check_matrix[138] = 11'b10001001000;
    assign parity_check_matrix[139] = 11'b10001010000;
    assign parity_check_matrix[140] = 11'b10001100000;
    assign parity_check_matrix[141] = 11'b10010000001;
    assign parity_check_matrix[142] = 11'b10010000010;
    assign parity_check_matrix[143] = 11'b10010000100;
    assign parity_check_matrix[144] = 11'b10010001000;
    assign parity_check_matrix[145] = 11'b10010010000;
    assign parity_check_matrix[146] = 11'b10010100000;
    assign parity_check_matrix[147] = 11'b10011000000;
    assign parity_check_matrix[148] = 11'b10100000001;
    assign parity_check_matrix[149] = 11'b10100000010;
    assign parity_check_matrix[150] = 11'b10100000100;
    assign parity_check_matrix[151] = 11'b10100001000;
    assign parity_check_matrix[152] = 11'b10100010000;
    assign parity_check_matrix[153] = 11'b10100100000;
    assign parity_check_matrix[154] = 11'b10101000000;
    assign parity_check_matrix[155] = 11'b10110000000;
    assign parity_check_matrix[156] = 11'b11000000001;
    assign parity_check_matrix[157] = 11'b11000000010;
    assign parity_check_matrix[158] = 11'b11000000100;
    assign parity_check_matrix[159] = 11'b11000001000;
    assign parity_check_matrix[160] = 11'b11000010000;
    assign parity_check_matrix[161] = 11'b11000100000;
    assign parity_check_matrix[162] = 11'b11001000000;
    assign parity_check_matrix[163] = 11'b11010000000;
    assign parity_check_matrix[164] = 11'b11100000000;
    assign parity_check_matrix[165] = 11'b00000011111;
    assign parity_check_matrix[166] = 11'b00000101111;
    assign parity_check_matrix[167] = 11'b00000110111;
    assign parity_check_matrix[168] = 11'b00000111011;
    assign parity_check_matrix[169] = 11'b00000111101;
    assign parity_check_matrix[170] = 11'b00000111110;
    assign parity_check_matrix[171] = 11'b00001001111;
    assign parity_check_matrix[172] = 11'b00001010111;
    assign parity_check_matrix[173] = 11'b00001011011;
    assign parity_check_matrix[174] = 11'b00001011101;
    assign parity_check_matrix[175] = 11'b00001011110;
    assign parity_check_matrix[176] = 11'b00001100111;
    assign parity_check_matrix[177] = 11'b00001101011;
    assign parity_check_matrix[178] = 11'b00001101101;
    assign parity_check_matrix[179] = 11'b00001101110;
    assign parity_check_matrix[180] = 11'b00001110011;
    assign parity_check_matrix[181] = 11'b00001110101;
    assign parity_check_matrix[182] = 11'b00001110110;
    assign parity_check_matrix[183] = 11'b00001111001;
    assign parity_check_matrix[184] = 11'b00001111010;
    assign parity_check_matrix[185] = 11'b00001111100;
    assign parity_check_matrix[186] = 11'b00010001111;
    assign parity_check_matrix[187] = 11'b00010010111;
    assign parity_check_matrix[188] = 11'b00010011011;
    assign parity_check_matrix[189] = 11'b00010011101;
    assign parity_check_matrix[190] = 11'b00010011110;
    assign parity_check_matrix[191] = 11'b00010100111;
    assign parity_check_matrix[192] = 11'b00010101011;
    assign parity_check_matrix[193] = 11'b00010101101;
    assign parity_check_matrix[194] = 11'b00010101110;
    assign parity_check_matrix[195] = 11'b00010110011;
    assign parity_check_matrix[196] = 11'b00010110101;
    assign parity_check_matrix[197] = 11'b00010110110;
    assign parity_check_matrix[198] = 11'b00010111001;
    assign parity_check_matrix[199] = 11'b00010111010;
    assign parity_check_matrix[200] = 11'b00010111100;
    assign parity_check_matrix[201] = 11'b00011000111;
    assign parity_check_matrix[202] = 11'b00011001011;
    assign parity_check_matrix[203] = 11'b00011001101;
    assign parity_check_matrix[204] = 11'b00011001110;
    assign parity_check_matrix[205] = 11'b00011010011;
    assign parity_check_matrix[206] = 11'b00011010101;
    assign parity_check_matrix[207] = 11'b00011010110;
    assign parity_check_matrix[208] = 11'b00011011001;
    assign parity_check_matrix[209] = 11'b00011011010;
    assign parity_check_matrix[210] = 11'b00011011100;
    assign parity_check_matrix[211] = 11'b00011100011;
    assign parity_check_matrix[212] = 11'b00011100101;
    assign parity_check_matrix[213] = 11'b00011100110;
    assign parity_check_matrix[214] = 11'b00011101001;
    assign parity_check_matrix[215] = 11'b00011101010;
    assign parity_check_matrix[216] = 11'b00011101100;
    assign parity_check_matrix[217] = 11'b00011110001;
    assign parity_check_matrix[218] = 11'b00011110010;
    assign parity_check_matrix[219] = 11'b00011110100;
    assign parity_check_matrix[220] = 11'b00011111000;
    assign parity_check_matrix[221] = 11'b00100001111;
    assign parity_check_matrix[222] = 11'b00100010111;
    assign parity_check_matrix[223] = 11'b00100011011;
    assign parity_check_matrix[224] = 11'b00100011101;
    assign parity_check_matrix[225] = 11'b00100011110;
    assign parity_check_matrix[226] = 11'b00100100111;
    assign parity_check_matrix[227] = 11'b00100101011;
    assign parity_check_matrix[228] = 11'b00100101101;
    assign parity_check_matrix[229] = 11'b00100101110;
    assign parity_check_matrix[230] = 11'b00100110011;
    assign parity_check_matrix[231] = 11'b00100110101;
    assign parity_check_matrix[232] = 11'b00100110110;
    assign parity_check_matrix[233] = 11'b00100111001;
    assign parity_check_matrix[234] = 11'b00100111010;
    assign parity_check_matrix[235] = 11'b00100111100;
    assign parity_check_matrix[236] = 11'b00101000111;
    assign parity_check_matrix[237] = 11'b00101001011;
    assign parity_check_matrix[238] = 11'b00101001101;
    assign parity_check_matrix[239] = 11'b00101001110;
    assign parity_check_matrix[240] = 11'b00101010011;
    assign parity_check_matrix[241] = 11'b00101010101;
    assign parity_check_matrix[242] = 11'b00101010110;
    assign parity_check_matrix[243] = 11'b00101011001;
    assign parity_check_matrix[244] = 11'b00101011010;
    assign parity_check_matrix[245] = 11'b00101011100;
    assign parity_check_matrix[246] = 11'b00101100011;
    assign parity_check_matrix[247] = 11'b00101100101;
    assign parity_check_matrix[248] = 11'b00101100110;
    assign parity_check_matrix[249] = 11'b00101101001;
    assign parity_check_matrix[250] = 11'b00101101010;
    assign parity_check_matrix[251] = 11'b00101101100;
    assign parity_check_matrix[252] = 11'b00101110001;
    assign parity_check_matrix[253] = 11'b00101110010;
    assign parity_check_matrix[254] = 11'b00101110100;
    assign parity_check_matrix[255] = 11'b00101111000;
    assign parity_check_matrix[256] = 11'b00110000111;
    assign parity_check_matrix[257] = 11'b00110001011;
    assign parity_check_matrix[258] = 11'b00110001101;
    assign parity_check_matrix[259] = 11'b00110001110;
    assign parity_check_matrix[260] = 11'b00110010011;
    assign parity_check_matrix[261] = 11'b00110010101;
    assign parity_check_matrix[262] = 11'b00110010110;
    assign parity_check_matrix[263] = 11'b00110011001;
    assign parity_check_matrix[264] = 11'b00110011010;
    assign parity_check_matrix[265] = 11'b00110011100;
    assign parity_check_matrix[266] = 11'b00110100011;
    assign parity_check_matrix[267] = 11'b00110100101;
    assign parity_check_matrix[268] = 11'b00110100110;
    assign parity_check_matrix[269] = 11'b00110101001;
    assign parity_check_matrix[270] = 11'b00110101010;
    assign parity_check_matrix[271] = 11'b00110101100;
    assign parity_check_matrix[272] = 11'b00110110001;
    assign parity_check_matrix[273] = 11'b00110110010;
    assign parity_check_matrix[274] = 11'b00110110100;
    assign parity_check_matrix[275] = 11'b00110111000;
    assign parity_check_matrix[276] = 11'b00111000011;
    assign parity_check_matrix[277] = 11'b00111000101;
    assign parity_check_matrix[278] = 11'b00111000110;
    assign parity_check_matrix[279] = 11'b00111001001;
    assign parity_check_matrix[280] = 11'b00111001010;
    assign parity_check_matrix[281] = 11'b00111001100;
    assign parity_check_matrix[282] = 11'b00111010001;
    assign parity_check_matrix[283] = 11'b00111010010;
    assign parity_check_matrix[284] = 11'b00111010100;
    assign parity_check_matrix[285] = 11'b00111011000;
    assign parity_check_matrix[286] = 11'b00111100001;
    assign parity_check_matrix[287] = 11'b00111100010;
    assign parity_check_matrix[288] = 11'b00111100100;
    assign parity_check_matrix[289] = 11'b00111101000;
    assign parity_check_matrix[290] = 11'b00111110000;
    assign parity_check_matrix[291] = 11'b01000001111;
    assign parity_check_matrix[292] = 11'b01000010111;
    assign parity_check_matrix[293] = 11'b01000011011;
    assign parity_check_matrix[294] = 11'b01000011101;
    assign parity_check_matrix[295] = 11'b01000011110;
    assign parity_check_matrix[296] = 11'b01000100111;
    assign parity_check_matrix[297] = 11'b01000101011;
    assign parity_check_matrix[298] = 11'b01000101101;
    assign parity_check_matrix[299] = 11'b01000101110;
    assign parity_check_matrix[300] = 11'b01000110011;
    assign parity_check_matrix[301] = 11'b01000110101;
    assign parity_check_matrix[302] = 11'b01000110110;
    assign parity_check_matrix[303] = 11'b01000111001;
    assign parity_check_matrix[304] = 11'b01000111010;
    assign parity_check_matrix[305] = 11'b01000111100;
    assign parity_check_matrix[306] = 11'b01001000111;
    assign parity_check_matrix[307] = 11'b01001001011;
    assign parity_check_matrix[308] = 11'b01001001101;
    assign parity_check_matrix[309] = 11'b01001001110;
    assign parity_check_matrix[310] = 11'b01001010011;
    assign parity_check_matrix[311] = 11'b01001010101;
    assign parity_check_matrix[312] = 11'b01001010110;
    assign parity_check_matrix[313] = 11'b01001011001;
    assign parity_check_matrix[314] = 11'b01001011010;
    assign parity_check_matrix[315] = 11'b01001011100;
    assign parity_check_matrix[316] = 11'b01001100011;
    assign parity_check_matrix[317] = 11'b01001100101;
    assign parity_check_matrix[318] = 11'b01001100110;
    assign parity_check_matrix[319] = 11'b01001101001;
    assign parity_check_matrix[320] = 11'b01001101010;
    assign parity_check_matrix[321] = 11'b01001101100;
    assign parity_check_matrix[322] = 11'b01001110001;
    assign parity_check_matrix[323] = 11'b01001110010;
    assign parity_check_matrix[324] = 11'b01001110100;
    assign parity_check_matrix[325] = 11'b01001111000;
    assign parity_check_matrix[326] = 11'b01010000111;
    assign parity_check_matrix[327] = 11'b01010001011;
    assign parity_check_matrix[328] = 11'b01010001101;
    assign parity_check_matrix[329] = 11'b01010001110;
    assign parity_check_matrix[330] = 11'b01010010011;
    assign parity_check_matrix[331] = 11'b01010010101;
    assign parity_check_matrix[332] = 11'b01010010110;
    assign parity_check_matrix[333] = 11'b01010011001;
    assign parity_check_matrix[334] = 11'b01010011010;
    assign parity_check_matrix[335] = 11'b01010011100;
    assign parity_check_matrix[336] = 11'b01010100011;
    assign parity_check_matrix[337] = 11'b01010100101;
    assign parity_check_matrix[338] = 11'b01010100110;
    assign parity_check_matrix[339] = 11'b01010101001;
    assign parity_check_matrix[340] = 11'b01010101010;
    assign parity_check_matrix[341] = 11'b01010101100;
    assign parity_check_matrix[342] = 11'b01010110001;
    assign parity_check_matrix[343] = 11'b01010110010;
    assign parity_check_matrix[344] = 11'b01010110100;
    assign parity_check_matrix[345] = 11'b01010111000;
    assign parity_check_matrix[346] = 11'b01011000011;
    assign parity_check_matrix[347] = 11'b01011000101;
    assign parity_check_matrix[348] = 11'b01011000110;
    assign parity_check_matrix[349] = 11'b01011001001;
    assign parity_check_matrix[350] = 11'b01011001010;
    assign parity_check_matrix[351] = 11'b01011001100;
    assign parity_check_matrix[352] = 11'b01011010001;
    assign parity_check_matrix[353] = 11'b01011010010;
    assign parity_check_matrix[354] = 11'b01011010100;
    assign parity_check_matrix[355] = 11'b01011011000;
    assign parity_check_matrix[356] = 11'b01011100001;
    assign parity_check_matrix[357] = 11'b01011100010;
    assign parity_check_matrix[358] = 11'b01011100100;
    assign parity_check_matrix[359] = 11'b01011101000;
    assign parity_check_matrix[360] = 11'b01011110000;
    assign parity_check_matrix[361] = 11'b01100000111;
    assign parity_check_matrix[362] = 11'b01100001011;
    assign parity_check_matrix[363] = 11'b01100001101;
    assign parity_check_matrix[364] = 11'b01100001110;
    assign parity_check_matrix[365] = 11'b01100010011;
    assign parity_check_matrix[366] = 11'b01100010101;
    assign parity_check_matrix[367] = 11'b01100010110;
    assign parity_check_matrix[368] = 11'b01100011001;
    assign parity_check_matrix[369] = 11'b01100011010;
    assign parity_check_matrix[370] = 11'b01100011100;
    assign parity_check_matrix[371] = 11'b01100100011;
    assign parity_check_matrix[372] = 11'b01100100101;
    assign parity_check_matrix[373] = 11'b01100100110;
    assign parity_check_matrix[374] = 11'b01100101001;
    assign parity_check_matrix[375] = 11'b01100101010;
    assign parity_check_matrix[376] = 11'b01100101100;
    assign parity_check_matrix[377] = 11'b01100110001;
    assign parity_check_matrix[378] = 11'b01100110010;
    assign parity_check_matrix[379] = 11'b01100110100;
    assign parity_check_matrix[380] = 11'b01100111000;
    assign parity_check_matrix[381] = 11'b01101000011;
    assign parity_check_matrix[382] = 11'b01101000101;
    assign parity_check_matrix[383] = 11'b01101000110;
    assign parity_check_matrix[384] = 11'b01101001001;
    assign parity_check_matrix[385] = 11'b01101001010;
    assign parity_check_matrix[386] = 11'b01101001100;
    assign parity_check_matrix[387] = 11'b01101010001;
    assign parity_check_matrix[388] = 11'b01101010010;
    assign parity_check_matrix[389] = 11'b01101010100;
    assign parity_check_matrix[390] = 11'b01101011000;
    assign parity_check_matrix[391] = 11'b01101100001;
    assign parity_check_matrix[392] = 11'b01101100010;
    assign parity_check_matrix[393] = 11'b01101100100;
    assign parity_check_matrix[394] = 11'b01101101000;
    assign parity_check_matrix[395] = 11'b01101110000;
    assign parity_check_matrix[396] = 11'b01110000011;
    assign parity_check_matrix[397] = 11'b01110000101;
    assign parity_check_matrix[398] = 11'b01110000110;
    assign parity_check_matrix[399] = 11'b01110001001;
    assign parity_check_matrix[400] = 11'b01110001010;
    assign parity_check_matrix[401] = 11'b01110001100;
    assign parity_check_matrix[402] = 11'b01110010001;
    assign parity_check_matrix[403] = 11'b01110010010;
    assign parity_check_matrix[404] = 11'b01110010100;
    assign parity_check_matrix[405] = 11'b01110011000;
    assign parity_check_matrix[406] = 11'b01110100001;
    assign parity_check_matrix[407] = 11'b01110100010;
    assign parity_check_matrix[408] = 11'b01110100100;
    assign parity_check_matrix[409] = 11'b01110101000;
    assign parity_check_matrix[410] = 11'b01110110000;
    assign parity_check_matrix[411] = 11'b01111000001;
    assign parity_check_matrix[412] = 11'b01111000010;
    assign parity_check_matrix[413] = 11'b01111000100;
    assign parity_check_matrix[414] = 11'b01111001000;
    assign parity_check_matrix[415] = 11'b01111010000;
    assign parity_check_matrix[416] = 11'b01111100000;
    assign parity_check_matrix[417] = 11'b10000001111;
    assign parity_check_matrix[418] = 11'b10000010111;
    assign parity_check_matrix[419] = 11'b10000011011;
    assign parity_check_matrix[420] = 11'b10000011101;
    assign parity_check_matrix[421] = 11'b10000011110;
    assign parity_check_matrix[422] = 11'b10000100111;
    assign parity_check_matrix[423] = 11'b10000101011;
    assign parity_check_matrix[424] = 11'b10000101101;
    assign parity_check_matrix[425] = 11'b10000101110;
    assign parity_check_matrix[426] = 11'b10000110011;
    assign parity_check_matrix[427] = 11'b10000110101;
    assign parity_check_matrix[428] = 11'b10000110110;
    assign parity_check_matrix[429] = 11'b10000111001;
    assign parity_check_matrix[430] = 11'b10000111010;
    assign parity_check_matrix[431] = 11'b10000111100;
    assign parity_check_matrix[432] = 11'b10001000111;
    assign parity_check_matrix[433] = 11'b10001001011;
    assign parity_check_matrix[434] = 11'b10001001101;
    assign parity_check_matrix[435] = 11'b10001001110;
    assign parity_check_matrix[436] = 11'b10001010011;
    assign parity_check_matrix[437] = 11'b10001010101;
    assign parity_check_matrix[438] = 11'b10001010110;
    assign parity_check_matrix[439] = 11'b10001011001;
    assign parity_check_matrix[440] = 11'b10001011010;
    assign parity_check_matrix[441] = 11'b10001011100;
    assign parity_check_matrix[442] = 11'b10001100011;
    assign parity_check_matrix[443] = 11'b10001100101;
    assign parity_check_matrix[444] = 11'b10001100110;
    assign parity_check_matrix[445] = 11'b10001101001;
    assign parity_check_matrix[446] = 11'b10001101010;
    assign parity_check_matrix[447] = 11'b10001101100;
    assign parity_check_matrix[448] = 11'b10001110001;
    assign parity_check_matrix[449] = 11'b10001110010;
    assign parity_check_matrix[450] = 11'b10001110100;
    assign parity_check_matrix[451] = 11'b10001111000;
    assign parity_check_matrix[452] = 11'b10010000111;
    assign parity_check_matrix[453] = 11'b10010001011;
    assign parity_check_matrix[454] = 11'b10010001101;
    assign parity_check_matrix[455] = 11'b10010001110;
    assign parity_check_matrix[456] = 11'b10010010011;
    assign parity_check_matrix[457] = 11'b10010010101;
    assign parity_check_matrix[458] = 11'b10010010110;
    assign parity_check_matrix[459] = 11'b10010011001;
    assign parity_check_matrix[460] = 11'b10010011010;
    assign parity_check_matrix[461] = 11'b10010011100;
    assign parity_check_matrix[462] = 11'b10010100011;
    assign parity_check_matrix[463] = 11'b10010100101;
    assign parity_check_matrix[464] = 11'b10010100110;
    assign parity_check_matrix[465] = 11'b10010101001;
    assign parity_check_matrix[466] = 11'b10010101010;
    assign parity_check_matrix[467] = 11'b10010101100;
    assign parity_check_matrix[468] = 11'b10010110001;
    assign parity_check_matrix[469] = 11'b10010110010;
    assign parity_check_matrix[470] = 11'b10010110100;
    assign parity_check_matrix[471] = 11'b10010111000;
    assign parity_check_matrix[472] = 11'b10011000011;
    assign parity_check_matrix[473] = 11'b10011000101;
    assign parity_check_matrix[474] = 11'b10011000110;
    assign parity_check_matrix[475] = 11'b10011001001;
    assign parity_check_matrix[476] = 11'b10011001010;
    assign parity_check_matrix[477] = 11'b10011001100;
    assign parity_check_matrix[478] = 11'b10011010001;
    assign parity_check_matrix[479] = 11'b10011010010;
    assign parity_check_matrix[480] = 11'b10011010100;
    assign parity_check_matrix[481] = 11'b10011011000;
    assign parity_check_matrix[482] = 11'b10011100001;
    assign parity_check_matrix[483] = 11'b10011100010;
    assign parity_check_matrix[484] = 11'b10011100100;
    assign parity_check_matrix[485] = 11'b10011101000;
    assign parity_check_matrix[486] = 11'b10011110000;
    assign parity_check_matrix[487] = 11'b10100000111;
    assign parity_check_matrix[488] = 11'b10100001011;
    assign parity_check_matrix[489] = 11'b10100001101;
    assign parity_check_matrix[490] = 11'b10100001110;
    assign parity_check_matrix[491] = 11'b10100010011;
    assign parity_check_matrix[492] = 11'b10100010101;
    assign parity_check_matrix[493] = 11'b10100010110;
    assign parity_check_matrix[494] = 11'b10100011001;
    assign parity_check_matrix[495] = 11'b10100011010;
    assign parity_check_matrix[496] = 11'b10100011100;
    assign parity_check_matrix[497] = 11'b10100100011;
    assign parity_check_matrix[498] = 11'b10100100101;
    assign parity_check_matrix[499] = 11'b10100100110;
    assign parity_check_matrix[500] = 11'b10100101001;
    assign parity_check_matrix[501] = 11'b10100101010;
    assign parity_check_matrix[502] = 11'b10100101100;
    assign parity_check_matrix[503] = 11'b10100110001;
    assign parity_check_matrix[504] = 11'b10100110010;
    assign parity_check_matrix[505] = 11'b10100110100;
    assign parity_check_matrix[506] = 11'b10100111000;
    assign parity_check_matrix[507] = 11'b10101000011;
    assign parity_check_matrix[508] = 11'b10101000101;
    assign parity_check_matrix[509] = 11'b10101000110;
    assign parity_check_matrix[510] = 11'b10101001001;
    assign parity_check_matrix[511] = 11'b10101001010;
    assign parity_check_matrix[512] = 11'b10000000000;
    assign parity_check_matrix[513] = 11'b01000000000;
    assign parity_check_matrix[514] = 11'b00100000000;
    assign parity_check_matrix[515] = 11'b00010000000;
    assign parity_check_matrix[516] = 11'b00001000000;
    assign parity_check_matrix[517] = 11'b00000100000;
    assign parity_check_matrix[518] = 11'b00000010000;
    assign parity_check_matrix[519] = 11'b00000001000;
    assign parity_check_matrix[520] = 11'b00000000100;
    assign parity_check_matrix[521] = 11'b00000000010;
    assign parity_check_matrix[522] = 11'b00000000001;
  end else if ((CodewordWidth == 1036) && (MessageWidth == 1024)) begin : gen_1036_1024
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 12)
    assign syndrome[0] = codeword[165] ^ codeword[166] ^ codeword[167] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[175] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[191] ^ codeword[192] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[210] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[682] ^ codeword[683] ^ codeword[684] ^ codeword[685] ^ codeword[686] ^ codeword[687] ^ codeword[688] ^ codeword[689] ^ codeword[690] ^ codeword[691] ^ codeword[692] ^ codeword[693] ^ codeword[694] ^ codeword[695] ^ codeword[696] ^ codeword[697] ^ codeword[698] ^ codeword[699] ^ codeword[700] ^ codeword[701] ^ codeword[702] ^ codeword[703] ^ codeword[704] ^ codeword[705] ^ codeword[706] ^ codeword[707] ^ codeword[708] ^ codeword[709] ^ codeword[710] ^ codeword[711] ^ codeword[712] ^ codeword[713] ^ codeword[714] ^ codeword[715] ^ codeword[716] ^ codeword[717] ^ codeword[718] ^ codeword[719] ^ codeword[720] ^ codeword[721] ^ codeword[722] ^ codeword[723] ^ codeword[724] ^ codeword[725] ^ codeword[726] ^ codeword[727] ^ codeword[728] ^ codeword[729] ^ codeword[730] ^ codeword[731] ^ codeword[732] ^ codeword[733] ^ codeword[734] ^ codeword[735] ^ codeword[736] ^ codeword[737] ^ codeword[738] ^ codeword[739] ^ codeword[740] ^ codeword[741] ^ codeword[742] ^ codeword[743] ^ codeword[744] ^ codeword[745] ^ codeword[746] ^ codeword[747] ^ codeword[748] ^ codeword[749] ^ codeword[750] ^ codeword[751] ^ codeword[752] ^ codeword[753] ^ codeword[754] ^ codeword[755] ^ codeword[756] ^ codeword[757] ^ codeword[758] ^ codeword[759] ^ codeword[760] ^ codeword[761] ^ codeword[762] ^ codeword[763] ^ codeword[764] ^ codeword[765] ^ codeword[766] ^ codeword[767] ^ codeword[768] ^ codeword[769] ^ codeword[770] ^ codeword[771] ^ codeword[772] ^ codeword[773] ^ codeword[774] ^ codeword[775] ^ codeword[776] ^ codeword[777] ^ codeword[778] ^ codeword[779] ^ codeword[780] ^ codeword[781] ^ codeword[782] ^ codeword[783] ^ codeword[784] ^ codeword[785] ^ codeword[786] ^ codeword[787] ^ codeword[788] ^ codeword[789] ^ codeword[790] ^ codeword[791] ^ codeword[792] ^ codeword[793] ^ codeword[794] ^ codeword[795] ^ codeword[796] ^ codeword[797] ^ codeword[798] ^ codeword[799] ^ codeword[800] ^ codeword[801] ^ codeword[802] ^ codeword[803] ^ codeword[804] ^ codeword[805] ^ codeword[806] ^ codeword[807] ^ codeword[808] ^ codeword[809] ^ codeword[810] ^ codeword[811] ^ codeword[812] ^ codeword[813] ^ codeword[814] ^ codeword[815] ^ codeword[816] ^ codeword[817] ^ codeword[818] ^ codeword[819] ^ codeword[820] ^ codeword[821] ^ codeword[822] ^ codeword[823] ^ codeword[824] ^ codeword[825] ^ codeword[826] ^ codeword[827] ^ codeword[828] ^ codeword[829] ^ codeword[830] ^ codeword[831] ^ codeword[832] ^ codeword[833] ^ codeword[834] ^ codeword[835] ^ codeword[836] ^ codeword[837] ^ codeword[838] ^ codeword[839] ^ codeword[840] ^ codeword[841] ^ codeword[842] ^ codeword[843] ^ codeword[844] ^ codeword[845] ^ codeword[846] ^ codeword[847] ^ codeword[848] ^ codeword[849] ^ codeword[850] ^ codeword[851] ^ codeword[852] ^ codeword[853] ^ codeword[854] ^ codeword[855] ^ codeword[856] ^ codeword[857] ^ codeword[858] ^ codeword[859] ^ codeword[860] ^ codeword[861] ^ codeword[862] ^ codeword[863] ^ codeword[864] ^ codeword[865] ^ codeword[866] ^ codeword[867] ^ codeword[868] ^ codeword[869] ^ codeword[870] ^ codeword[871] ^ codeword[872] ^ codeword[873] ^ codeword[874] ^ codeword[875] ^ codeword[876] ^ codeword[877] ^ codeword[878] ^ codeword[879] ^ codeword[880] ^ codeword[881] ^ codeword[882] ^ codeword[883] ^ codeword[884] ^ codeword[885] ^ codeword[886] ^ codeword[887] ^ codeword[888] ^ codeword[889] ^ codeword[890] ^ codeword[891] ^ codeword[892] ^ codeword[893] ^ codeword[894] ^ codeword[895] ^ codeword[896] ^ codeword[897] ^ codeword[898] ^ codeword[899] ^ codeword[900] ^ codeword[901] ^ codeword[902] ^ codeword[903] ^ codeword[904] ^ codeword[905] ^ codeword[906] ^ codeword[907] ^ codeword[908] ^ codeword[909] ^ codeword[910] ^ codeword[911] ^ codeword[912] ^ codeword[913] ^ codeword[914] ^ codeword[915] ^ codeword[916] ^ codeword[917] ^ codeword[918] ^ codeword[919] ^ codeword[920] ^ codeword[921] ^ codeword[922] ^ codeword[923] ^ codeword[924] ^ codeword[925] ^ codeword[926] ^ codeword[927] ^ codeword[928] ^ codeword[929] ^ codeword[930] ^ codeword[931] ^ codeword[932] ^ codeword[933] ^ codeword[934] ^ codeword[935] ^ codeword[936] ^ codeword[937] ^ codeword[938] ^ codeword[939] ^ codeword[940] ^ codeword[941] ^ codeword[942] ^ codeword[943] ^ codeword[944] ^ codeword[945] ^ codeword[946] ^ codeword[947] ^ codeword[948] ^ codeword[949] ^ codeword[950] ^ codeword[951] ^ codeword[952] ^ codeword[953] ^ codeword[954] ^ codeword[955] ^ codeword[956] ^ codeword[957] ^ codeword[958] ^ codeword[959] ^ codeword[960] ^ codeword[961] ^ codeword[962] ^ codeword[963] ^ codeword[964] ^ codeword[965] ^ codeword[966] ^ codeword[967] ^ codeword[968] ^ codeword[969] ^ codeword[970] ^ codeword[971] ^ codeword[972] ^ codeword[973] ^ codeword[974] ^ codeword[975] ^ codeword[976] ^ codeword[977] ^ codeword[978] ^ codeword[979] ^ codeword[980] ^ codeword[981] ^ codeword[982] ^ codeword[983] ^ codeword[984] ^ codeword[985] ^ codeword[986] ^ codeword[987] ^ codeword[988] ^ codeword[989] ^ codeword[990] ^ codeword[991] ^ codeword[992] ^ codeword[993] ^ codeword[994] ^ codeword[995] ^ codeword[996] ^ codeword[997] ^ codeword[998] ^ codeword[999] ^ codeword[1000] ^ codeword[1001] ^ codeword[1002] ^ codeword[1003] ^ codeword[1004] ^ codeword[1005] ^ codeword[1006] ^ codeword[1007] ^ codeword[1008] ^ codeword[1009] ^ codeword[1010] ^ codeword[1011] ^ codeword[1024];
    assign syndrome[1] = codeword[120] ^ codeword[121] ^ codeword[122] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[210] ^ codeword[211] ^ codeword[212] ^ codeword[213] ^ codeword[214] ^ codeword[215] ^ codeword[216] ^ codeword[217] ^ codeword[218] ^ codeword[219] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[511] ^ codeword[512] ^ codeword[513] ^ codeword[514] ^ codeword[515] ^ codeword[516] ^ codeword[517] ^ codeword[518] ^ codeword[519] ^ codeword[520] ^ codeword[521] ^ codeword[522] ^ codeword[523] ^ codeword[524] ^ codeword[525] ^ codeword[526] ^ codeword[527] ^ codeword[528] ^ codeword[529] ^ codeword[530] ^ codeword[531] ^ codeword[532] ^ codeword[533] ^ codeword[534] ^ codeword[535] ^ codeword[536] ^ codeword[537] ^ codeword[538] ^ codeword[539] ^ codeword[540] ^ codeword[541] ^ codeword[542] ^ codeword[543] ^ codeword[544] ^ codeword[545] ^ codeword[546] ^ codeword[547] ^ codeword[548] ^ codeword[549] ^ codeword[550] ^ codeword[551] ^ codeword[552] ^ codeword[553] ^ codeword[554] ^ codeword[555] ^ codeword[556] ^ codeword[557] ^ codeword[558] ^ codeword[559] ^ codeword[560] ^ codeword[561] ^ codeword[562] ^ codeword[563] ^ codeword[564] ^ codeword[565] ^ codeword[566] ^ codeword[567] ^ codeword[568] ^ codeword[569] ^ codeword[570] ^ codeword[571] ^ codeword[572] ^ codeword[573] ^ codeword[574] ^ codeword[575] ^ codeword[576] ^ codeword[577] ^ codeword[578] ^ codeword[579] ^ codeword[580] ^ codeword[581] ^ codeword[582] ^ codeword[583] ^ codeword[584] ^ codeword[585] ^ codeword[586] ^ codeword[587] ^ codeword[588] ^ codeword[589] ^ codeword[590] ^ codeword[591] ^ codeword[592] ^ codeword[593] ^ codeword[594] ^ codeword[595] ^ codeword[596] ^ codeword[597] ^ codeword[598] ^ codeword[599] ^ codeword[600] ^ codeword[601] ^ codeword[602] ^ codeword[603] ^ codeword[604] ^ codeword[605] ^ codeword[606] ^ codeword[607] ^ codeword[608] ^ codeword[609] ^ codeword[610] ^ codeword[611] ^ codeword[612] ^ codeword[613] ^ codeword[614] ^ codeword[615] ^ codeword[616] ^ codeword[617] ^ codeword[618] ^ codeword[619] ^ codeword[620] ^ codeword[621] ^ codeword[622] ^ codeword[623] ^ codeword[624] ^ codeword[625] ^ codeword[626] ^ codeword[627] ^ codeword[628] ^ codeword[629] ^ codeword[630] ^ codeword[631] ^ codeword[632] ^ codeword[633] ^ codeword[634] ^ codeword[635] ^ codeword[636] ^ codeword[637] ^ codeword[638] ^ codeword[639] ^ codeword[640] ^ codeword[641] ^ codeword[642] ^ codeword[643] ^ codeword[644] ^ codeword[645] ^ codeword[646] ^ codeword[647] ^ codeword[648] ^ codeword[649] ^ codeword[650] ^ codeword[651] ^ codeword[652] ^ codeword[653] ^ codeword[654] ^ codeword[655] ^ codeword[656] ^ codeword[657] ^ codeword[658] ^ codeword[659] ^ codeword[660] ^ codeword[661] ^ codeword[662] ^ codeword[663] ^ codeword[664] ^ codeword[665] ^ codeword[666] ^ codeword[667] ^ codeword[668] ^ codeword[669] ^ codeword[670] ^ codeword[671] ^ codeword[672] ^ codeword[673] ^ codeword[674] ^ codeword[675] ^ codeword[676] ^ codeword[677] ^ codeword[678] ^ codeword[679] ^ codeword[680] ^ codeword[681] ^ codeword[892] ^ codeword[893] ^ codeword[894] ^ codeword[895] ^ codeword[896] ^ codeword[897] ^ codeword[898] ^ codeword[899] ^ codeword[900] ^ codeword[901] ^ codeword[902] ^ codeword[903] ^ codeword[904] ^ codeword[905] ^ codeword[906] ^ codeword[907] ^ codeword[908] ^ codeword[909] ^ codeword[910] ^ codeword[911] ^ codeword[912] ^ codeword[913] ^ codeword[914] ^ codeword[915] ^ codeword[916] ^ codeword[917] ^ codeword[918] ^ codeword[919] ^ codeword[920] ^ codeword[921] ^ codeword[922] ^ codeword[923] ^ codeword[924] ^ codeword[925] ^ codeword[926] ^ codeword[927] ^ codeword[928] ^ codeword[929] ^ codeword[930] ^ codeword[931] ^ codeword[932] ^ codeword[933] ^ codeword[934] ^ codeword[935] ^ codeword[936] ^ codeword[937] ^ codeword[938] ^ codeword[939] ^ codeword[940] ^ codeword[941] ^ codeword[942] ^ codeword[943] ^ codeword[944] ^ codeword[945] ^ codeword[946] ^ codeword[947] ^ codeword[948] ^ codeword[949] ^ codeword[950] ^ codeword[951] ^ codeword[952] ^ codeword[953] ^ codeword[954] ^ codeword[955] ^ codeword[956] ^ codeword[957] ^ codeword[958] ^ codeword[959] ^ codeword[960] ^ codeword[961] ^ codeword[962] ^ codeword[963] ^ codeword[964] ^ codeword[965] ^ codeword[966] ^ codeword[967] ^ codeword[968] ^ codeword[969] ^ codeword[970] ^ codeword[971] ^ codeword[972] ^ codeword[973] ^ codeword[974] ^ codeword[975] ^ codeword[976] ^ codeword[977] ^ codeword[978] ^ codeword[979] ^ codeword[980] ^ codeword[981] ^ codeword[982] ^ codeword[983] ^ codeword[984] ^ codeword[985] ^ codeword[986] ^ codeword[987] ^ codeword[988] ^ codeword[989] ^ codeword[990] ^ codeword[991] ^ codeword[992] ^ codeword[993] ^ codeword[994] ^ codeword[995] ^ codeword[996] ^ codeword[997] ^ codeword[998] ^ codeword[999] ^ codeword[1000] ^ codeword[1001] ^ codeword[1002] ^ codeword[1003] ^ codeword[1004] ^ codeword[1005] ^ codeword[1006] ^ codeword[1007] ^ codeword[1008] ^ codeword[1009] ^ codeword[1010] ^ codeword[1011] ^ codeword[1025];
    assign syndrome[2] = codeword[84] ^ codeword[85] ^ codeword[86] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[156] ^ codeword[157] ^ codeword[158] ^ codeword[159] ^ codeword[160] ^ codeword[161] ^ codeword[162] ^ codeword[163] ^ codeword[164] ^ codeword[201] ^ codeword[202] ^ codeword[203] ^ codeword[204] ^ codeword[205] ^ codeword[206] ^ codeword[207] ^ codeword[208] ^ codeword[209] ^ codeword[219] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[416] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[420] ^ codeword[421] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[598] ^ codeword[599] ^ codeword[600] ^ codeword[601] ^ codeword[602] ^ codeword[603] ^ codeword[604] ^ codeword[605] ^ codeword[606] ^ codeword[607] ^ codeword[608] ^ codeword[609] ^ codeword[610] ^ codeword[611] ^ codeword[612] ^ codeword[613] ^ codeword[614] ^ codeword[615] ^ codeword[616] ^ codeword[617] ^ codeword[618] ^ codeword[619] ^ codeword[620] ^ codeword[621] ^ codeword[622] ^ codeword[623] ^ codeword[624] ^ codeword[625] ^ codeword[626] ^ codeword[627] ^ codeword[628] ^ codeword[629] ^ codeword[630] ^ codeword[631] ^ codeword[632] ^ codeword[633] ^ codeword[634] ^ codeword[635] ^ codeword[636] ^ codeword[637] ^ codeword[638] ^ codeword[639] ^ codeword[640] ^ codeword[641] ^ codeword[642] ^ codeword[643] ^ codeword[644] ^ codeword[645] ^ codeword[646] ^ codeword[647] ^ codeword[648] ^ codeword[649] ^ codeword[650] ^ codeword[651] ^ codeword[652] ^ codeword[653] ^ codeword[654] ^ codeword[655] ^ codeword[656] ^ codeword[657] ^ codeword[658] ^ codeword[659] ^ codeword[660] ^ codeword[661] ^ codeword[662] ^ codeword[663] ^ codeword[664] ^ codeword[665] ^ codeword[666] ^ codeword[667] ^ codeword[668] ^ codeword[669] ^ codeword[670] ^ codeword[671] ^ codeword[672] ^ codeword[673] ^ codeword[674] ^ codeword[675] ^ codeword[676] ^ codeword[677] ^ codeword[678] ^ codeword[679] ^ codeword[680] ^ codeword[681] ^ codeword[808] ^ codeword[809] ^ codeword[810] ^ codeword[811] ^ codeword[812] ^ codeword[813] ^ codeword[814] ^ codeword[815] ^ codeword[816] ^ codeword[817] ^ codeword[818] ^ codeword[819] ^ codeword[820] ^ codeword[821] ^ codeword[822] ^ codeword[823] ^ codeword[824] ^ codeword[825] ^ codeword[826] ^ codeword[827] ^ codeword[828] ^ codeword[829] ^ codeword[830] ^ codeword[831] ^ codeword[832] ^ codeword[833] ^ codeword[834] ^ codeword[835] ^ codeword[836] ^ codeword[837] ^ codeword[838] ^ codeword[839] ^ codeword[840] ^ codeword[841] ^ codeword[842] ^ codeword[843] ^ codeword[844] ^ codeword[845] ^ codeword[846] ^ codeword[847] ^ codeword[848] ^ codeword[849] ^ codeword[850] ^ codeword[851] ^ codeword[852] ^ codeword[853] ^ codeword[854] ^ codeword[855] ^ codeword[856] ^ codeword[857] ^ codeword[858] ^ codeword[859] ^ codeword[860] ^ codeword[861] ^ codeword[862] ^ codeword[863] ^ codeword[864] ^ codeword[865] ^ codeword[866] ^ codeword[867] ^ codeword[868] ^ codeword[869] ^ codeword[870] ^ codeword[871] ^ codeword[872] ^ codeword[873] ^ codeword[874] ^ codeword[875] ^ codeword[876] ^ codeword[877] ^ codeword[878] ^ codeword[879] ^ codeword[880] ^ codeword[881] ^ codeword[882] ^ codeword[883] ^ codeword[884] ^ codeword[885] ^ codeword[886] ^ codeword[887] ^ codeword[888] ^ codeword[889] ^ codeword[890] ^ codeword[891] ^ codeword[976] ^ codeword[977] ^ codeword[978] ^ codeword[979] ^ codeword[980] ^ codeword[981] ^ codeword[982] ^ codeword[983] ^ codeword[984] ^ codeword[985] ^ codeword[986] ^ codeword[987] ^ codeword[988] ^ codeword[989] ^ codeword[990] ^ codeword[991] ^ codeword[992] ^ codeword[993] ^ codeword[994] ^ codeword[995] ^ codeword[996] ^ codeword[997] ^ codeword[998] ^ codeword[999] ^ codeword[1000] ^ codeword[1001] ^ codeword[1002] ^ codeword[1003] ^ codeword[1004] ^ codeword[1005] ^ codeword[1006] ^ codeword[1007] ^ codeword[1008] ^ codeword[1009] ^ codeword[1010] ^ codeword[1011] ^ codeword[1026];
    assign syndrome[3] = codeword[56] ^ codeword[57] ^ codeword[58] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[112] ^ codeword[113] ^ codeword[114] ^ codeword[115] ^ codeword[116] ^ codeword[117] ^ codeword[118] ^ codeword[119] ^ codeword[148] ^ codeword[149] ^ codeword[150] ^ codeword[151] ^ codeword[152] ^ codeword[153] ^ codeword[154] ^ codeword[155] ^ codeword[164] ^ codeword[193] ^ codeword[194] ^ codeword[195] ^ codeword[196] ^ codeword[197] ^ codeword[198] ^ codeword[199] ^ codeword[200] ^ codeword[209] ^ codeword[218] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[295] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[416] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[420] ^ codeword[421] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[451] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[542] ^ codeword[543] ^ codeword[544] ^ codeword[545] ^ codeword[546] ^ codeword[547] ^ codeword[548] ^ codeword[549] ^ codeword[550] ^ codeword[551] ^ codeword[552] ^ codeword[553] ^ codeword[554] ^ codeword[555] ^ codeword[556] ^ codeword[557] ^ codeword[558] ^ codeword[559] ^ codeword[560] ^ codeword[561] ^ codeword[562] ^ codeword[563] ^ codeword[564] ^ codeword[565] ^ codeword[566] ^ codeword[567] ^ codeword[568] ^ codeword[569] ^ codeword[570] ^ codeword[571] ^ codeword[572] ^ codeword[573] ^ codeword[574] ^ codeword[575] ^ codeword[576] ^ codeword[577] ^ codeword[578] ^ codeword[579] ^ codeword[580] ^ codeword[581] ^ codeword[582] ^ codeword[583] ^ codeword[584] ^ codeword[585] ^ codeword[586] ^ codeword[587] ^ codeword[588] ^ codeword[589] ^ codeword[590] ^ codeword[591] ^ codeword[592] ^ codeword[593] ^ codeword[594] ^ codeword[595] ^ codeword[596] ^ codeword[597] ^ codeword[654] ^ codeword[655] ^ codeword[656] ^ codeword[657] ^ codeword[658] ^ codeword[659] ^ codeword[660] ^ codeword[661] ^ codeword[662] ^ codeword[663] ^ codeword[664] ^ codeword[665] ^ codeword[666] ^ codeword[667] ^ codeword[668] ^ codeword[669] ^ codeword[670] ^ codeword[671] ^ codeword[672] ^ codeword[673] ^ codeword[674] ^ codeword[675] ^ codeword[676] ^ codeword[677] ^ codeword[678] ^ codeword[679] ^ codeword[680] ^ codeword[681] ^ codeword[752] ^ codeword[753] ^ codeword[754] ^ codeword[755] ^ codeword[756] ^ codeword[757] ^ codeword[758] ^ codeword[759] ^ codeword[760] ^ codeword[761] ^ codeword[762] ^ codeword[763] ^ codeword[764] ^ codeword[765] ^ codeword[766] ^ codeword[767] ^ codeword[768] ^ codeword[769] ^ codeword[770] ^ codeword[771] ^ codeword[772] ^ codeword[773] ^ codeword[774] ^ codeword[775] ^ codeword[776] ^ codeword[777] ^ codeword[778] ^ codeword[779] ^ codeword[780] ^ codeword[781] ^ codeword[782] ^ codeword[783] ^ codeword[784] ^ codeword[785] ^ codeword[786] ^ codeword[787] ^ codeword[788] ^ codeword[789] ^ codeword[790] ^ codeword[791] ^ codeword[792] ^ codeword[793] ^ codeword[794] ^ codeword[795] ^ codeword[796] ^ codeword[797] ^ codeword[798] ^ codeword[799] ^ codeword[800] ^ codeword[801] ^ codeword[802] ^ codeword[803] ^ codeword[804] ^ codeword[805] ^ codeword[806] ^ codeword[807] ^ codeword[864] ^ codeword[865] ^ codeword[866] ^ codeword[867] ^ codeword[868] ^ codeword[869] ^ codeword[870] ^ codeword[871] ^ codeword[872] ^ codeword[873] ^ codeword[874] ^ codeword[875] ^ codeword[876] ^ codeword[877] ^ codeword[878] ^ codeword[879] ^ codeword[880] ^ codeword[881] ^ codeword[882] ^ codeword[883] ^ codeword[884] ^ codeword[885] ^ codeword[886] ^ codeword[887] ^ codeword[888] ^ codeword[889] ^ codeword[890] ^ codeword[891] ^ codeword[948] ^ codeword[949] ^ codeword[950] ^ codeword[951] ^ codeword[952] ^ codeword[953] ^ codeword[954] ^ codeword[955] ^ codeword[956] ^ codeword[957] ^ codeword[958] ^ codeword[959] ^ codeword[960] ^ codeword[961] ^ codeword[962] ^ codeword[963] ^ codeword[964] ^ codeword[965] ^ codeword[966] ^ codeword[967] ^ codeword[968] ^ codeword[969] ^ codeword[970] ^ codeword[971] ^ codeword[972] ^ codeword[973] ^ codeword[974] ^ codeword[975] ^ codeword[1004] ^ codeword[1005] ^ codeword[1006] ^ codeword[1007] ^ codeword[1008] ^ codeword[1009] ^ codeword[1010] ^ codeword[1011] ^ codeword[1020] ^ codeword[1021] ^ codeword[1022] ^ codeword[1023] ^ codeword[1027];
    assign syndrome[4] = codeword[35] ^ codeword[36] ^ codeword[37] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[77] ^ codeword[78] ^ codeword[79] ^ codeword[80] ^ codeword[81] ^ codeword[82] ^ codeword[83] ^ codeword[105] ^ codeword[106] ^ codeword[107] ^ codeword[108] ^ codeword[109] ^ codeword[110] ^ codeword[111] ^ codeword[119] ^ codeword[141] ^ codeword[142] ^ codeword[143] ^ codeword[144] ^ codeword[145] ^ codeword[146] ^ codeword[147] ^ codeword[155] ^ codeword[163] ^ codeword[186] ^ codeword[187] ^ codeword[188] ^ codeword[189] ^ codeword[190] ^ codeword[191] ^ codeword[192] ^ codeword[200] ^ codeword[208] ^ codeword[217] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[315] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[451] ^ codeword[452] ^ codeword[453] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[511] ^ codeword[512] ^ codeword[513] ^ codeword[514] ^ codeword[515] ^ codeword[516] ^ codeword[517] ^ codeword[518] ^ codeword[519] ^ codeword[520] ^ codeword[521] ^ codeword[522] ^ codeword[523] ^ codeword[524] ^ codeword[525] ^ codeword[526] ^ codeword[527] ^ codeword[528] ^ codeword[529] ^ codeword[530] ^ codeword[531] ^ codeword[532] ^ codeword[533] ^ codeword[534] ^ codeword[535] ^ codeword[536] ^ codeword[537] ^ codeword[538] ^ codeword[539] ^ codeword[540] ^ codeword[541] ^ codeword[577] ^ codeword[578] ^ codeword[579] ^ codeword[580] ^ codeword[581] ^ codeword[582] ^ codeword[583] ^ codeword[584] ^ codeword[585] ^ codeword[586] ^ codeword[587] ^ codeword[588] ^ codeword[589] ^ codeword[590] ^ codeword[591] ^ codeword[592] ^ codeword[593] ^ codeword[594] ^ codeword[595] ^ codeword[596] ^ codeword[597] ^ codeword[633] ^ codeword[634] ^ codeword[635] ^ codeword[636] ^ codeword[637] ^ codeword[638] ^ codeword[639] ^ codeword[640] ^ codeword[641] ^ codeword[642] ^ codeword[643] ^ codeword[644] ^ codeword[645] ^ codeword[646] ^ codeword[647] ^ codeword[648] ^ codeword[649] ^ codeword[650] ^ codeword[651] ^ codeword[652] ^ codeword[653] ^ codeword[675] ^ codeword[676] ^ codeword[677] ^ codeword[678] ^ codeword[679] ^ codeword[680] ^ codeword[681] ^ codeword[717] ^ codeword[718] ^ codeword[719] ^ codeword[720] ^ codeword[721] ^ codeword[722] ^ codeword[723] ^ codeword[724] ^ codeword[725] ^ codeword[726] ^ codeword[727] ^ codeword[728] ^ codeword[729] ^ codeword[730] ^ codeword[731] ^ codeword[732] ^ codeword[733] ^ codeword[734] ^ codeword[735] ^ codeword[736] ^ codeword[737] ^ codeword[738] ^ codeword[739] ^ codeword[740] ^ codeword[741] ^ codeword[742] ^ codeword[743] ^ codeword[744] ^ codeword[745] ^ codeword[746] ^ codeword[747] ^ codeword[748] ^ codeword[749] ^ codeword[750] ^ codeword[751] ^ codeword[787] ^ codeword[788] ^ codeword[789] ^ codeword[790] ^ codeword[791] ^ codeword[792] ^ codeword[793] ^ codeword[794] ^ codeword[795] ^ codeword[796] ^ codeword[797] ^ codeword[798] ^ codeword[799] ^ codeword[800] ^ codeword[801] ^ codeword[802] ^ codeword[803] ^ codeword[804] ^ codeword[805] ^ codeword[806] ^ codeword[807] ^ codeword[843] ^ codeword[844] ^ codeword[845] ^ codeword[846] ^ codeword[847] ^ codeword[848] ^ codeword[849] ^ codeword[850] ^ codeword[851] ^ codeword[852] ^ codeword[853] ^ codeword[854] ^ codeword[855] ^ codeword[856] ^ codeword[857] ^ codeword[858] ^ codeword[859] ^ codeword[860] ^ codeword[861] ^ codeword[862] ^ codeword[863] ^ codeword[885] ^ codeword[886] ^ codeword[887] ^ codeword[888] ^ codeword[889] ^ codeword[890] ^ codeword[891] ^ codeword[927] ^ codeword[928] ^ codeword[929] ^ codeword[930] ^ codeword[931] ^ codeword[932] ^ codeword[933] ^ codeword[934] ^ codeword[935] ^ codeword[936] ^ codeword[937] ^ codeword[938] ^ codeword[939] ^ codeword[940] ^ codeword[941] ^ codeword[942] ^ codeword[943] ^ codeword[944] ^ codeword[945] ^ codeword[946] ^ codeword[947] ^ codeword[969] ^ codeword[970] ^ codeword[971] ^ codeword[972] ^ codeword[973] ^ codeword[974] ^ codeword[975] ^ codeword[997] ^ codeword[998] ^ codeword[999] ^ codeword[1000] ^ codeword[1001] ^ codeword[1002] ^ codeword[1003] ^ codeword[1011] ^ codeword[1013] ^ codeword[1014] ^ codeword[1015] ^ codeword[1016] ^ codeword[1017] ^ codeword[1018] ^ codeword[1019] ^ codeword[1028];
    assign syndrome[5] = codeword[20] ^ codeword[21] ^ codeword[22] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[50] ^ codeword[51] ^ codeword[52] ^ codeword[53] ^ codeword[54] ^ codeword[55] ^ codeword[71] ^ codeword[72] ^ codeword[73] ^ codeword[74] ^ codeword[75] ^ codeword[76] ^ codeword[83] ^ codeword[99] ^ codeword[100] ^ codeword[101] ^ codeword[102] ^ codeword[103] ^ codeword[104] ^ codeword[111] ^ codeword[118] ^ codeword[135] ^ codeword[136] ^ codeword[137] ^ codeword[138] ^ codeword[139] ^ codeword[140] ^ codeword[147] ^ codeword[154] ^ codeword[162] ^ codeword[180] ^ codeword[181] ^ codeword[182] ^ codeword[183] ^ codeword[184] ^ codeword[185] ^ codeword[192] ^ codeword[199] ^ codeword[207] ^ codeword[216] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[295] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[331] ^ codeword[332] ^ codeword[333] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[401] ^ codeword[402] ^ codeword[403] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[436] ^ codeword[437] ^ codeword[438] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[466] ^ codeword[467] ^ codeword[468] ^ codeword[469] ^ codeword[470] ^ codeword[471] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[527] ^ codeword[528] ^ codeword[529] ^ codeword[530] ^ codeword[531] ^ codeword[532] ^ codeword[533] ^ codeword[534] ^ codeword[535] ^ codeword[536] ^ codeword[537] ^ codeword[538] ^ codeword[539] ^ codeword[540] ^ codeword[541] ^ codeword[562] ^ codeword[563] ^ codeword[564] ^ codeword[565] ^ codeword[566] ^ codeword[567] ^ codeword[568] ^ codeword[569] ^ codeword[570] ^ codeword[571] ^ codeword[572] ^ codeword[573] ^ codeword[574] ^ codeword[575] ^ codeword[576] ^ codeword[592] ^ codeword[593] ^ codeword[594] ^ codeword[595] ^ codeword[596] ^ codeword[597] ^ codeword[618] ^ codeword[619] ^ codeword[620] ^ codeword[621] ^ codeword[622] ^ codeword[623] ^ codeword[624] ^ codeword[625] ^ codeword[626] ^ codeword[627] ^ codeword[628] ^ codeword[629] ^ codeword[630] ^ codeword[631] ^ codeword[632] ^ codeword[648] ^ codeword[649] ^ codeword[650] ^ codeword[651] ^ codeword[652] ^ codeword[653] ^ codeword[669] ^ codeword[670] ^ codeword[671] ^ codeword[672] ^ codeword[673] ^ codeword[674] ^ codeword[681] ^ codeword[697] ^ codeword[698] ^ codeword[699] ^ codeword[700] ^ codeword[701] ^ codeword[702] ^ codeword[703] ^ codeword[704] ^ codeword[705] ^ codeword[706] ^ codeword[707] ^ codeword[708] ^ codeword[709] ^ codeword[710] ^ codeword[711] ^ codeword[712] ^ codeword[713] ^ codeword[714] ^ codeword[715] ^ codeword[716] ^ codeword[737] ^ codeword[738] ^ codeword[739] ^ codeword[740] ^ codeword[741] ^ codeword[742] ^ codeword[743] ^ codeword[744] ^ codeword[745] ^ codeword[746] ^ codeword[747] ^ codeword[748] ^ codeword[749] ^ codeword[750] ^ codeword[751] ^ codeword[772] ^ codeword[773] ^ codeword[774] ^ codeword[775] ^ codeword[776] ^ codeword[777] ^ codeword[778] ^ codeword[779] ^ codeword[780] ^ codeword[781] ^ codeword[782] ^ codeword[783] ^ codeword[784] ^ codeword[785] ^ codeword[786] ^ codeword[802] ^ codeword[803] ^ codeword[804] ^ codeword[805] ^ codeword[806] ^ codeword[807] ^ codeword[828] ^ codeword[829] ^ codeword[830] ^ codeword[831] ^ codeword[832] ^ codeword[833] ^ codeword[834] ^ codeword[835] ^ codeword[836] ^ codeword[837] ^ codeword[838] ^ codeword[839] ^ codeword[840] ^ codeword[841] ^ codeword[842] ^ codeword[858] ^ codeword[859] ^ codeword[860] ^ codeword[861] ^ codeword[862] ^ codeword[863] ^ codeword[879] ^ codeword[880] ^ codeword[881] ^ codeword[882] ^ codeword[883] ^ codeword[884] ^ codeword[891] ^ codeword[912] ^ codeword[913] ^ codeword[914] ^ codeword[915] ^ codeword[916] ^ codeword[917] ^ codeword[918] ^ codeword[919] ^ codeword[920] ^ codeword[921] ^ codeword[922] ^ codeword[923] ^ codeword[924] ^ codeword[925] ^ codeword[926] ^ codeword[942] ^ codeword[943] ^ codeword[944] ^ codeword[945] ^ codeword[946] ^ codeword[947] ^ codeword[963] ^ codeword[964] ^ codeword[965] ^ codeword[966] ^ codeword[967] ^ codeword[968] ^ codeword[975] ^ codeword[991] ^ codeword[992] ^ codeword[993] ^ codeword[994] ^ codeword[995] ^ codeword[996] ^ codeword[1003] ^ codeword[1010] ^ codeword[1012] ^ codeword[1014] ^ codeword[1015] ^ codeword[1016] ^ codeword[1017] ^ codeword[1018] ^ codeword[1019] ^ codeword[1021] ^ codeword[1022] ^ codeword[1023] ^ codeword[1029];
    assign syndrome[6] = codeword[10] ^ codeword[11] ^ codeword[12] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[30] ^ codeword[31] ^ codeword[32] ^ codeword[33] ^ codeword[34] ^ codeword[45] ^ codeword[46] ^ codeword[47] ^ codeword[48] ^ codeword[49] ^ codeword[55] ^ codeword[66] ^ codeword[67] ^ codeword[68] ^ codeword[69] ^ codeword[70] ^ codeword[76] ^ codeword[82] ^ codeword[94] ^ codeword[95] ^ codeword[96] ^ codeword[97] ^ codeword[98] ^ codeword[104] ^ codeword[110] ^ codeword[117] ^ codeword[130] ^ codeword[131] ^ codeword[132] ^ codeword[133] ^ codeword[134] ^ codeword[140] ^ codeword[146] ^ codeword[153] ^ codeword[161] ^ codeword[175] ^ codeword[176] ^ codeword[177] ^ codeword[178] ^ codeword[179] ^ codeword[185] ^ codeword[191] ^ codeword[198] ^ codeword[206] ^ codeword[215] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[266] ^ codeword[267] ^ codeword[268] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[301] ^ codeword[302] ^ codeword[303] ^ codeword[304] ^ codeword[305] ^ codeword[306] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[321] ^ codeword[322] ^ codeword[323] ^ codeword[324] ^ codeword[325] ^ codeword[326] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[341] ^ codeword[342] ^ codeword[343] ^ codeword[344] ^ codeword[345] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[371] ^ codeword[372] ^ codeword[373] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[391] ^ codeword[392] ^ codeword[393] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[411] ^ codeword[412] ^ codeword[413] ^ codeword[414] ^ codeword[415] ^ codeword[426] ^ codeword[427] ^ codeword[428] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[446] ^ codeword[447] ^ codeword[448] ^ codeword[449] ^ codeword[450] ^ codeword[461] ^ codeword[462] ^ codeword[463] ^ codeword[464] ^ codeword[465] ^ codeword[471] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[497] ^ codeword[498] ^ codeword[499] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[517] ^ codeword[518] ^ codeword[519] ^ codeword[520] ^ codeword[521] ^ codeword[522] ^ codeword[523] ^ codeword[524] ^ codeword[525] ^ codeword[526] ^ codeword[537] ^ codeword[538] ^ codeword[539] ^ codeword[540] ^ codeword[541] ^ codeword[552] ^ codeword[553] ^ codeword[554] ^ codeword[555] ^ codeword[556] ^ codeword[557] ^ codeword[558] ^ codeword[559] ^ codeword[560] ^ codeword[561] ^ codeword[572] ^ codeword[573] ^ codeword[574] ^ codeword[575] ^ codeword[576] ^ codeword[587] ^ codeword[588] ^ codeword[589] ^ codeword[590] ^ codeword[591] ^ codeword[597] ^ codeword[608] ^ codeword[609] ^ codeword[610] ^ codeword[611] ^ codeword[612] ^ codeword[613] ^ codeword[614] ^ codeword[615] ^ codeword[616] ^ codeword[617] ^ codeword[628] ^ codeword[629] ^ codeword[630] ^ codeword[631] ^ codeword[632] ^ codeword[643] ^ codeword[644] ^ codeword[645] ^ codeword[646] ^ codeword[647] ^ codeword[653] ^ codeword[664] ^ codeword[665] ^ codeword[666] ^ codeword[667] ^ codeword[668] ^ codeword[674] ^ codeword[680] ^ codeword[687] ^ codeword[688] ^ codeword[689] ^ codeword[690] ^ codeword[691] ^ codeword[692] ^ codeword[693] ^ codeword[694] ^ codeword[695] ^ codeword[696] ^ codeword[707] ^ codeword[708] ^ codeword[709] ^ codeword[710] ^ codeword[711] ^ codeword[712] ^ codeword[713] ^ codeword[714] ^ codeword[715] ^ codeword[716] ^ codeword[727] ^ codeword[728] ^ codeword[729] ^ codeword[730] ^ codeword[731] ^ codeword[732] ^ codeword[733] ^ codeword[734] ^ codeword[735] ^ codeword[736] ^ codeword[747] ^ codeword[748] ^ codeword[749] ^ codeword[750] ^ codeword[751] ^ codeword[762] ^ codeword[763] ^ codeword[764] ^ codeword[765] ^ codeword[766] ^ codeword[767] ^ codeword[768] ^ codeword[769] ^ codeword[770] ^ codeword[771] ^ codeword[782] ^ codeword[783] ^ codeword[784] ^ codeword[785] ^ codeword[786] ^ codeword[797] ^ codeword[798] ^ codeword[799] ^ codeword[800] ^ codeword[801] ^ codeword[807] ^ codeword[818] ^ codeword[819] ^ codeword[820] ^ codeword[821] ^ codeword[822] ^ codeword[823] ^ codeword[824] ^ codeword[825] ^ codeword[826] ^ codeword[827] ^ codeword[838] ^ codeword[839] ^ codeword[840] ^ codeword[841] ^ codeword[842] ^ codeword[853] ^ codeword[854] ^ codeword[855] ^ codeword[856] ^ codeword[857] ^ codeword[863] ^ codeword[874] ^ codeword[875] ^ codeword[876] ^ codeword[877] ^ codeword[878] ^ codeword[884] ^ codeword[890] ^ codeword[902] ^ codeword[903] ^ codeword[904] ^ codeword[905] ^ codeword[906] ^ codeword[907] ^ codeword[908] ^ codeword[909] ^ codeword[910] ^ codeword[911] ^ codeword[922] ^ codeword[923] ^ codeword[924] ^ codeword[925] ^ codeword[926] ^ codeword[937] ^ codeword[938] ^ codeword[939] ^ codeword[940] ^ codeword[941] ^ codeword[947] ^ codeword[958] ^ codeword[959] ^ codeword[960] ^ codeword[961] ^ codeword[962] ^ codeword[968] ^ codeword[974] ^ codeword[986] ^ codeword[987] ^ codeword[988] ^ codeword[989] ^ codeword[990] ^ codeword[996] ^ codeword[1002] ^ codeword[1009] ^ codeword[1012] ^ codeword[1013] ^ codeword[1015] ^ codeword[1016] ^ codeword[1017] ^ codeword[1018] ^ codeword[1019] ^ codeword[1020] ^ codeword[1022] ^ codeword[1023] ^ codeword[1030];
    assign syndrome[7] = codeword[4] ^ codeword[5] ^ codeword[6] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[16] ^ codeword[17] ^ codeword[18] ^ codeword[19] ^ codeword[26] ^ codeword[27] ^ codeword[28] ^ codeword[29] ^ codeword[34] ^ codeword[41] ^ codeword[42] ^ codeword[43] ^ codeword[44] ^ codeword[49] ^ codeword[54] ^ codeword[62] ^ codeword[63] ^ codeword[64] ^ codeword[65] ^ codeword[70] ^ codeword[75] ^ codeword[81] ^ codeword[90] ^ codeword[91] ^ codeword[92] ^ codeword[93] ^ codeword[98] ^ codeword[103] ^ codeword[109] ^ codeword[116] ^ codeword[126] ^ codeword[127] ^ codeword[128] ^ codeword[129] ^ codeword[134] ^ codeword[139] ^ codeword[145] ^ codeword[152] ^ codeword[160] ^ codeword[171] ^ codeword[172] ^ codeword[173] ^ codeword[174] ^ codeword[179] ^ codeword[184] ^ codeword[190] ^ codeword[197] ^ codeword[205] ^ codeword[214] ^ codeword[220] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[235] ^ codeword[236] ^ codeword[237] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[250] ^ codeword[251] ^ codeword[252] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[260] ^ codeword[261] ^ codeword[262] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[272] ^ codeword[273] ^ codeword[274] ^ codeword[275] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[285] ^ codeword[286] ^ codeword[287] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[295] ^ codeword[296] ^ codeword[297] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[307] ^ codeword[308] ^ codeword[309] ^ codeword[310] ^ codeword[315] ^ codeword[316] ^ codeword[317] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[327] ^ codeword[328] ^ codeword[329] ^ codeword[330] ^ codeword[337] ^ codeword[338] ^ codeword[339] ^ codeword[340] ^ codeword[345] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[355] ^ codeword[356] ^ codeword[357] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[365] ^ codeword[366] ^ codeword[367] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[377] ^ codeword[378] ^ codeword[379] ^ codeword[380] ^ codeword[385] ^ codeword[386] ^ codeword[387] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[397] ^ codeword[398] ^ codeword[399] ^ codeword[400] ^ codeword[407] ^ codeword[408] ^ codeword[409] ^ codeword[410] ^ codeword[415] ^ codeword[420] ^ codeword[421] ^ codeword[422] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[432] ^ codeword[433] ^ codeword[434] ^ codeword[435] ^ codeword[442] ^ codeword[443] ^ codeword[444] ^ codeword[445] ^ codeword[450] ^ codeword[457] ^ codeword[458] ^ codeword[459] ^ codeword[460] ^ codeword[465] ^ codeword[470] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[481] ^ codeword[482] ^ codeword[483] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[491] ^ codeword[492] ^ codeword[493] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[503] ^ codeword[504] ^ codeword[505] ^ codeword[506] ^ codeword[511] ^ codeword[512] ^ codeword[513] ^ codeword[514] ^ codeword[515] ^ codeword[516] ^ codeword[523] ^ codeword[524] ^ codeword[525] ^ codeword[526] ^ codeword[533] ^ codeword[534] ^ codeword[535] ^ codeword[536] ^ codeword[541] ^ codeword[546] ^ codeword[547] ^ codeword[548] ^ codeword[549] ^ codeword[550] ^ codeword[551] ^ codeword[558] ^ codeword[559] ^ codeword[560] ^ codeword[561] ^ codeword[568] ^ codeword[569] ^ codeword[570] ^ codeword[571] ^ codeword[576] ^ codeword[583] ^ codeword[584] ^ codeword[585] ^ codeword[586] ^ codeword[591] ^ codeword[596] ^ codeword[602] ^ codeword[603] ^ codeword[604] ^ codeword[605] ^ codeword[606] ^ codeword[607] ^ codeword[614] ^ codeword[615] ^ codeword[616] ^ codeword[617] ^ codeword[624] ^ codeword[625] ^ codeword[626] ^ codeword[627] ^ codeword[632] ^ codeword[639] ^ codeword[640] ^ codeword[641] ^ codeword[642] ^ codeword[647] ^ codeword[652] ^ codeword[660] ^ codeword[661] ^ codeword[662] ^ codeword[663] ^ codeword[668] ^ codeword[673] ^ codeword[679] ^ codeword[683] ^ codeword[684] ^ codeword[685] ^ codeword[686] ^ codeword[691] ^ codeword[692] ^ codeword[693] ^ codeword[694] ^ codeword[695] ^ codeword[696] ^ codeword[701] ^ codeword[702] ^ codeword[703] ^ codeword[704] ^ codeword[705] ^ codeword[706] ^ codeword[713] ^ codeword[714] ^ codeword[715] ^ codeword[716] ^ codeword[721] ^ codeword[722] ^ codeword[723] ^ codeword[724] ^ codeword[725] ^ codeword[726] ^ codeword[733] ^ codeword[734] ^ codeword[735] ^ codeword[736] ^ codeword[743] ^ codeword[744] ^ codeword[745] ^ codeword[746] ^ codeword[751] ^ codeword[756] ^ codeword[757] ^ codeword[758] ^ codeword[759] ^ codeword[760] ^ codeword[761] ^ codeword[768] ^ codeword[769] ^ codeword[770] ^ codeword[771] ^ codeword[778] ^ codeword[779] ^ codeword[780] ^ codeword[781] ^ codeword[786] ^ codeword[793] ^ codeword[794] ^ codeword[795] ^ codeword[796] ^ codeword[801] ^ codeword[806] ^ codeword[812] ^ codeword[813] ^ codeword[814] ^ codeword[815] ^ codeword[816] ^ codeword[817] ^ codeword[824] ^ codeword[825] ^ codeword[826] ^ codeword[827] ^ codeword[834] ^ codeword[835] ^ codeword[836] ^ codeword[837] ^ codeword[842] ^ codeword[849] ^ codeword[850] ^ codeword[851] ^ codeword[852] ^ codeword[857] ^ codeword[862] ^ codeword[870] ^ codeword[871] ^ codeword[872] ^ codeword[873] ^ codeword[878] ^ codeword[883] ^ codeword[889] ^ codeword[896] ^ codeword[897] ^ codeword[898] ^ codeword[899] ^ codeword[900] ^ codeword[901] ^ codeword[908] ^ codeword[909] ^ codeword[910] ^ codeword[911] ^ codeword[918] ^ codeword[919] ^ codeword[920] ^ codeword[921] ^ codeword[926] ^ codeword[933] ^ codeword[934] ^ codeword[935] ^ codeword[936] ^ codeword[941] ^ codeword[946] ^ codeword[954] ^ codeword[955] ^ codeword[956] ^ codeword[957] ^ codeword[962] ^ codeword[967] ^ codeword[973] ^ codeword[982] ^ codeword[983] ^ codeword[984] ^ codeword[985] ^ codeword[990] ^ codeword[995] ^ codeword[1001] ^ codeword[1008] ^ codeword[1012] ^ codeword[1013] ^ codeword[1014] ^ codeword[1016] ^ codeword[1017] ^ codeword[1018] ^ codeword[1019] ^ codeword[1020] ^ codeword[1021] ^ codeword[1023] ^ codeword[1031];
    assign syndrome[8] = codeword[1] ^ codeword[2] ^ codeword[3] ^ codeword[7] ^ codeword[8] ^ codeword[9] ^ codeword[13] ^ codeword[14] ^ codeword[15] ^ codeword[19] ^ codeword[23] ^ codeword[24] ^ codeword[25] ^ codeword[29] ^ codeword[33] ^ codeword[38] ^ codeword[39] ^ codeword[40] ^ codeword[44] ^ codeword[48] ^ codeword[53] ^ codeword[59] ^ codeword[60] ^ codeword[61] ^ codeword[65] ^ codeword[69] ^ codeword[74] ^ codeword[80] ^ codeword[87] ^ codeword[88] ^ codeword[89] ^ codeword[93] ^ codeword[97] ^ codeword[102] ^ codeword[108] ^ codeword[115] ^ codeword[123] ^ codeword[124] ^ codeword[125] ^ codeword[129] ^ codeword[133] ^ codeword[138] ^ codeword[144] ^ codeword[151] ^ codeword[159] ^ codeword[168] ^ codeword[169] ^ codeword[170] ^ codeword[174] ^ codeword[178] ^ codeword[183] ^ codeword[189] ^ codeword[196] ^ codeword[204] ^ codeword[213] ^ codeword[220] ^ codeword[221] ^ codeword[223] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[228] ^ codeword[229] ^ codeword[230] ^ codeword[232] ^ codeword[233] ^ codeword[234] ^ codeword[238] ^ codeword[239] ^ codeword[240] ^ codeword[241] ^ codeword[243] ^ codeword[244] ^ codeword[245] ^ codeword[247] ^ codeword[248] ^ codeword[249] ^ codeword[253] ^ codeword[254] ^ codeword[255] ^ codeword[257] ^ codeword[258] ^ codeword[259] ^ codeword[263] ^ codeword[264] ^ codeword[265] ^ codeword[269] ^ codeword[270] ^ codeword[271] ^ codeword[275] ^ codeword[276] ^ codeword[278] ^ codeword[279] ^ codeword[280] ^ codeword[282] ^ codeword[283] ^ codeword[284] ^ codeword[288] ^ codeword[289] ^ codeword[290] ^ codeword[292] ^ codeword[293] ^ codeword[294] ^ codeword[298] ^ codeword[299] ^ codeword[300] ^ codeword[304] ^ codeword[305] ^ codeword[306] ^ codeword[310] ^ codeword[312] ^ codeword[313] ^ codeword[314] ^ codeword[318] ^ codeword[319] ^ codeword[320] ^ codeword[324] ^ codeword[325] ^ codeword[326] ^ codeword[330] ^ codeword[334] ^ codeword[335] ^ codeword[336] ^ codeword[340] ^ codeword[344] ^ codeword[346] ^ codeword[348] ^ codeword[349] ^ codeword[350] ^ codeword[352] ^ codeword[353] ^ codeword[354] ^ codeword[358] ^ codeword[359] ^ codeword[360] ^ codeword[362] ^ codeword[363] ^ codeword[364] ^ codeword[368] ^ codeword[369] ^ codeword[370] ^ codeword[374] ^ codeword[375] ^ codeword[376] ^ codeword[380] ^ codeword[382] ^ codeword[383] ^ codeword[384] ^ codeword[388] ^ codeword[389] ^ codeword[390] ^ codeword[394] ^ codeword[395] ^ codeword[396] ^ codeword[400] ^ codeword[404] ^ codeword[405] ^ codeword[406] ^ codeword[410] ^ codeword[414] ^ codeword[417] ^ codeword[418] ^ codeword[419] ^ codeword[423] ^ codeword[424] ^ codeword[425] ^ codeword[429] ^ codeword[430] ^ codeword[431] ^ codeword[435] ^ codeword[439] ^ codeword[440] ^ codeword[441] ^ codeword[445] ^ codeword[449] ^ codeword[454] ^ codeword[455] ^ codeword[456] ^ codeword[460] ^ codeword[464] ^ codeword[469] ^ codeword[472] ^ codeword[474] ^ codeword[475] ^ codeword[476] ^ codeword[478] ^ codeword[479] ^ codeword[480] ^ codeword[484] ^ codeword[485] ^ codeword[486] ^ codeword[488] ^ codeword[489] ^ codeword[490] ^ codeword[494] ^ codeword[495] ^ codeword[496] ^ codeword[500] ^ codeword[501] ^ codeword[502] ^ codeword[506] ^ codeword[508] ^ codeword[509] ^ codeword[510] ^ codeword[514] ^ codeword[515] ^ codeword[516] ^ codeword[520] ^ codeword[521] ^ codeword[522] ^ codeword[526] ^ codeword[530] ^ codeword[531] ^ codeword[532] ^ codeword[536] ^ codeword[540] ^ codeword[543] ^ codeword[544] ^ codeword[545] ^ codeword[549] ^ codeword[550] ^ codeword[551] ^ codeword[555] ^ codeword[556] ^ codeword[557] ^ codeword[561] ^ codeword[565] ^ codeword[566] ^ codeword[567] ^ codeword[571] ^ codeword[575] ^ codeword[580] ^ codeword[581] ^ codeword[582] ^ codeword[586] ^ codeword[590] ^ codeword[595] ^ codeword[599] ^ codeword[600] ^ codeword[601] ^ codeword[605] ^ codeword[606] ^ codeword[607] ^ codeword[611] ^ codeword[612] ^ codeword[613] ^ codeword[617] ^ codeword[621] ^ codeword[622] ^ codeword[623] ^ codeword[627] ^ codeword[631] ^ codeword[636] ^ codeword[637] ^ codeword[638] ^ codeword[642] ^ codeword[646] ^ codeword[651] ^ codeword[657] ^ codeword[658] ^ codeword[659] ^ codeword[663] ^ codeword[667] ^ codeword[672] ^ codeword[678] ^ codeword[682] ^ codeword[684] ^ codeword[685] ^ codeword[686] ^ codeword[688] ^ codeword[689] ^ codeword[690] ^ codeword[694] ^ codeword[695] ^ codeword[696] ^ codeword[698] ^ codeword[699] ^ codeword[700] ^ codeword[704] ^ codeword[705] ^ codeword[706] ^ codeword[710] ^ codeword[711] ^ codeword[712] ^ codeword[716] ^ codeword[718] ^ codeword[719] ^ codeword[720] ^ codeword[724] ^ codeword[725] ^ codeword[726] ^ codeword[730] ^ codeword[731] ^ codeword[732] ^ codeword[736] ^ codeword[740] ^ codeword[741] ^ codeword[742] ^ codeword[746] ^ codeword[750] ^ codeword[753] ^ codeword[754] ^ codeword[755] ^ codeword[759] ^ codeword[760] ^ codeword[761] ^ codeword[765] ^ codeword[766] ^ codeword[767] ^ codeword[771] ^ codeword[775] ^ codeword[776] ^ codeword[777] ^ codeword[781] ^ codeword[785] ^ codeword[790] ^ codeword[791] ^ codeword[792] ^ codeword[796] ^ codeword[800] ^ codeword[805] ^ codeword[809] ^ codeword[810] ^ codeword[811] ^ codeword[815] ^ codeword[816] ^ codeword[817] ^ codeword[821] ^ codeword[822] ^ codeword[823] ^ codeword[827] ^ codeword[831] ^ codeword[832] ^ codeword[833] ^ codeword[837] ^ codeword[841] ^ codeword[846] ^ codeword[847] ^ codeword[848] ^ codeword[852] ^ codeword[856] ^ codeword[861] ^ codeword[867] ^ codeword[868] ^ codeword[869] ^ codeword[873] ^ codeword[877] ^ codeword[882] ^ codeword[888] ^ codeword[893] ^ codeword[894] ^ codeword[895] ^ codeword[899] ^ codeword[900] ^ codeword[901] ^ codeword[905] ^ codeword[906] ^ codeword[907] ^ codeword[911] ^ codeword[915] ^ codeword[916] ^ codeword[917] ^ codeword[921] ^ codeword[925] ^ codeword[930] ^ codeword[931] ^ codeword[932] ^ codeword[936] ^ codeword[940] ^ codeword[945] ^ codeword[951] ^ codeword[952] ^ codeword[953] ^ codeword[957] ^ codeword[961] ^ codeword[966] ^ codeword[972] ^ codeword[979] ^ codeword[980] ^ codeword[981] ^ codeword[985] ^ codeword[989] ^ codeword[994] ^ codeword[1000] ^ codeword[1007] ^ codeword[1012] ^ codeword[1013] ^ codeword[1014] ^ codeword[1015] ^ codeword[1017] ^ codeword[1018] ^ codeword[1019] ^ codeword[1020] ^ codeword[1021] ^ codeword[1022] ^ codeword[1032];
    assign syndrome[9] = codeword[0] ^ codeword[2] ^ codeword[3] ^ codeword[5] ^ codeword[6] ^ codeword[9] ^ codeword[11] ^ codeword[12] ^ codeword[15] ^ codeword[18] ^ codeword[21] ^ codeword[22] ^ codeword[25] ^ codeword[28] ^ codeword[32] ^ codeword[36] ^ codeword[37] ^ codeword[40] ^ codeword[43] ^ codeword[47] ^ codeword[52] ^ codeword[57] ^ codeword[58] ^ codeword[61] ^ codeword[64] ^ codeword[68] ^ codeword[73] ^ codeword[79] ^ codeword[85] ^ codeword[86] ^ codeword[89] ^ codeword[92] ^ codeword[96] ^ codeword[101] ^ codeword[107] ^ codeword[114] ^ codeword[121] ^ codeword[122] ^ codeword[125] ^ codeword[128] ^ codeword[132] ^ codeword[137] ^ codeword[143] ^ codeword[150] ^ codeword[158] ^ codeword[166] ^ codeword[167] ^ codeword[170] ^ codeword[173] ^ codeword[177] ^ codeword[182] ^ codeword[188] ^ codeword[195] ^ codeword[203] ^ codeword[212] ^ codeword[220] ^ codeword[221] ^ codeword[222] ^ codeword[224] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[229] ^ codeword[230] ^ codeword[231] ^ codeword[233] ^ codeword[234] ^ codeword[236] ^ codeword[237] ^ codeword[240] ^ codeword[241] ^ codeword[242] ^ codeword[244] ^ codeword[245] ^ codeword[246] ^ codeword[248] ^ codeword[249] ^ codeword[251] ^ codeword[252] ^ codeword[255] ^ codeword[256] ^ codeword[258] ^ codeword[259] ^ codeword[261] ^ codeword[262] ^ codeword[265] ^ codeword[267] ^ codeword[268] ^ codeword[271] ^ codeword[274] ^ codeword[276] ^ codeword[277] ^ codeword[279] ^ codeword[280] ^ codeword[281] ^ codeword[283] ^ codeword[284] ^ codeword[286] ^ codeword[287] ^ codeword[290] ^ codeword[291] ^ codeword[293] ^ codeword[294] ^ codeword[296] ^ codeword[297] ^ codeword[300] ^ codeword[302] ^ codeword[303] ^ codeword[306] ^ codeword[309] ^ codeword[311] ^ codeword[313] ^ codeword[314] ^ codeword[316] ^ codeword[317] ^ codeword[320] ^ codeword[322] ^ codeword[323] ^ codeword[326] ^ codeword[329] ^ codeword[332] ^ codeword[333] ^ codeword[336] ^ codeword[339] ^ codeword[343] ^ codeword[346] ^ codeword[347] ^ codeword[349] ^ codeword[350] ^ codeword[351] ^ codeword[353] ^ codeword[354] ^ codeword[356] ^ codeword[357] ^ codeword[360] ^ codeword[361] ^ codeword[363] ^ codeword[364] ^ codeword[366] ^ codeword[367] ^ codeword[370] ^ codeword[372] ^ codeword[373] ^ codeword[376] ^ codeword[379] ^ codeword[381] ^ codeword[383] ^ codeword[384] ^ codeword[386] ^ codeword[387] ^ codeword[390] ^ codeword[392] ^ codeword[393] ^ codeword[396] ^ codeword[399] ^ codeword[402] ^ codeword[403] ^ codeword[406] ^ codeword[409] ^ codeword[413] ^ codeword[416] ^ codeword[418] ^ codeword[419] ^ codeword[421] ^ codeword[422] ^ codeword[425] ^ codeword[427] ^ codeword[428] ^ codeword[431] ^ codeword[434] ^ codeword[437] ^ codeword[438] ^ codeword[441] ^ codeword[444] ^ codeword[448] ^ codeword[452] ^ codeword[453] ^ codeword[456] ^ codeword[459] ^ codeword[463] ^ codeword[468] ^ codeword[472] ^ codeword[473] ^ codeword[475] ^ codeword[476] ^ codeword[477] ^ codeword[479] ^ codeword[480] ^ codeword[482] ^ codeword[483] ^ codeword[486] ^ codeword[487] ^ codeword[489] ^ codeword[490] ^ codeword[492] ^ codeword[493] ^ codeword[496] ^ codeword[498] ^ codeword[499] ^ codeword[502] ^ codeword[505] ^ codeword[507] ^ codeword[509] ^ codeword[510] ^ codeword[512] ^ codeword[513] ^ codeword[516] ^ codeword[518] ^ codeword[519] ^ codeword[522] ^ codeword[525] ^ codeword[528] ^ codeword[529] ^ codeword[532] ^ codeword[535] ^ codeword[539] ^ codeword[542] ^ codeword[544] ^ codeword[545] ^ codeword[547] ^ codeword[548] ^ codeword[551] ^ codeword[553] ^ codeword[554] ^ codeword[557] ^ codeword[560] ^ codeword[563] ^ codeword[564] ^ codeword[567] ^ codeword[570] ^ codeword[574] ^ codeword[578] ^ codeword[579] ^ codeword[582] ^ codeword[585] ^ codeword[589] ^ codeword[594] ^ codeword[598] ^ codeword[600] ^ codeword[601] ^ codeword[603] ^ codeword[604] ^ codeword[607] ^ codeword[609] ^ codeword[610] ^ codeword[613] ^ codeword[616] ^ codeword[619] ^ codeword[620] ^ codeword[623] ^ codeword[626] ^ codeword[630] ^ codeword[634] ^ codeword[635] ^ codeword[638] ^ codeword[641] ^ codeword[645] ^ codeword[650] ^ codeword[655] ^ codeword[656] ^ codeword[659] ^ codeword[662] ^ codeword[666] ^ codeword[671] ^ codeword[677] ^ codeword[682] ^ codeword[683] ^ codeword[685] ^ codeword[686] ^ codeword[687] ^ codeword[689] ^ codeword[690] ^ codeword[692] ^ codeword[693] ^ codeword[696] ^ codeword[697] ^ codeword[699] ^ codeword[700] ^ codeword[702] ^ codeword[703] ^ codeword[706] ^ codeword[708] ^ codeword[709] ^ codeword[712] ^ codeword[715] ^ codeword[717] ^ codeword[719] ^ codeword[720] ^ codeword[722] ^ codeword[723] ^ codeword[726] ^ codeword[728] ^ codeword[729] ^ codeword[732] ^ codeword[735] ^ codeword[738] ^ codeword[739] ^ codeword[742] ^ codeword[745] ^ codeword[749] ^ codeword[752] ^ codeword[754] ^ codeword[755] ^ codeword[757] ^ codeword[758] ^ codeword[761] ^ codeword[763] ^ codeword[764] ^ codeword[767] ^ codeword[770] ^ codeword[773] ^ codeword[774] ^ codeword[777] ^ codeword[780] ^ codeword[784] ^ codeword[788] ^ codeword[789] ^ codeword[792] ^ codeword[795] ^ codeword[799] ^ codeword[804] ^ codeword[808] ^ codeword[810] ^ codeword[811] ^ codeword[813] ^ codeword[814] ^ codeword[817] ^ codeword[819] ^ codeword[820] ^ codeword[823] ^ codeword[826] ^ codeword[829] ^ codeword[830] ^ codeword[833] ^ codeword[836] ^ codeword[840] ^ codeword[844] ^ codeword[845] ^ codeword[848] ^ codeword[851] ^ codeword[855] ^ codeword[860] ^ codeword[865] ^ codeword[866] ^ codeword[869] ^ codeword[872] ^ codeword[876] ^ codeword[881] ^ codeword[887] ^ codeword[892] ^ codeword[894] ^ codeword[895] ^ codeword[897] ^ codeword[898] ^ codeword[901] ^ codeword[903] ^ codeword[904] ^ codeword[907] ^ codeword[910] ^ codeword[913] ^ codeword[914] ^ codeword[917] ^ codeword[920] ^ codeword[924] ^ codeword[928] ^ codeword[929] ^ codeword[932] ^ codeword[935] ^ codeword[939] ^ codeword[944] ^ codeword[949] ^ codeword[950] ^ codeword[953] ^ codeword[956] ^ codeword[960] ^ codeword[965] ^ codeword[971] ^ codeword[977] ^ codeword[978] ^ codeword[981] ^ codeword[984] ^ codeword[988] ^ codeword[993] ^ codeword[999] ^ codeword[1006] ^ codeword[1012] ^ codeword[1013] ^ codeword[1014] ^ codeword[1015] ^ codeword[1016] ^ codeword[1018] ^ codeword[1019] ^ codeword[1020] ^ codeword[1021] ^ codeword[1022] ^ codeword[1023] ^ codeword[1033];
    assign syndrome[10] = codeword[0] ^ codeword[1] ^ codeword[3] ^ codeword[4] ^ codeword[6] ^ codeword[8] ^ codeword[10] ^ codeword[12] ^ codeword[14] ^ codeword[17] ^ codeword[20] ^ codeword[22] ^ codeword[24] ^ codeword[27] ^ codeword[31] ^ codeword[35] ^ codeword[37] ^ codeword[39] ^ codeword[42] ^ codeword[46] ^ codeword[51] ^ codeword[56] ^ codeword[58] ^ codeword[60] ^ codeword[63] ^ codeword[67] ^ codeword[72] ^ codeword[78] ^ codeword[84] ^ codeword[86] ^ codeword[88] ^ codeword[91] ^ codeword[95] ^ codeword[100] ^ codeword[106] ^ codeword[113] ^ codeword[120] ^ codeword[122] ^ codeword[124] ^ codeword[127] ^ codeword[131] ^ codeword[136] ^ codeword[142] ^ codeword[149] ^ codeword[157] ^ codeword[165] ^ codeword[167] ^ codeword[169] ^ codeword[172] ^ codeword[176] ^ codeword[181] ^ codeword[187] ^ codeword[194] ^ codeword[202] ^ codeword[211] ^ codeword[220] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[225] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[230] ^ codeword[231] ^ codeword[232] ^ codeword[234] ^ codeword[235] ^ codeword[237] ^ codeword[239] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[245] ^ codeword[246] ^ codeword[247] ^ codeword[249] ^ codeword[250] ^ codeword[252] ^ codeword[254] ^ codeword[256] ^ codeword[257] ^ codeword[259] ^ codeword[260] ^ codeword[262] ^ codeword[264] ^ codeword[266] ^ codeword[268] ^ codeword[270] ^ codeword[273] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[280] ^ codeword[281] ^ codeword[282] ^ codeword[284] ^ codeword[285] ^ codeword[287] ^ codeword[289] ^ codeword[291] ^ codeword[292] ^ codeword[294] ^ codeword[295] ^ codeword[297] ^ codeword[299] ^ codeword[301] ^ codeword[303] ^ codeword[305] ^ codeword[308] ^ codeword[311] ^ codeword[312] ^ codeword[314] ^ codeword[315] ^ codeword[317] ^ codeword[319] ^ codeword[321] ^ codeword[323] ^ codeword[325] ^ codeword[328] ^ codeword[331] ^ codeword[333] ^ codeword[335] ^ codeword[338] ^ codeword[342] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[350] ^ codeword[351] ^ codeword[352] ^ codeword[354] ^ codeword[355] ^ codeword[357] ^ codeword[359] ^ codeword[361] ^ codeword[362] ^ codeword[364] ^ codeword[365] ^ codeword[367] ^ codeword[369] ^ codeword[371] ^ codeword[373] ^ codeword[375] ^ codeword[378] ^ codeword[381] ^ codeword[382] ^ codeword[384] ^ codeword[385] ^ codeword[387] ^ codeword[389] ^ codeword[391] ^ codeword[393] ^ codeword[395] ^ codeword[398] ^ codeword[401] ^ codeword[403] ^ codeword[405] ^ codeword[408] ^ codeword[412] ^ codeword[416] ^ codeword[417] ^ codeword[419] ^ codeword[420] ^ codeword[422] ^ codeword[424] ^ codeword[426] ^ codeword[428] ^ codeword[430] ^ codeword[433] ^ codeword[436] ^ codeword[438] ^ codeword[440] ^ codeword[443] ^ codeword[447] ^ codeword[451] ^ codeword[453] ^ codeword[455] ^ codeword[458] ^ codeword[462] ^ codeword[467] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[476] ^ codeword[477] ^ codeword[478] ^ codeword[480] ^ codeword[481] ^ codeword[483] ^ codeword[485] ^ codeword[487] ^ codeword[488] ^ codeword[490] ^ codeword[491] ^ codeword[493] ^ codeword[495] ^ codeword[497] ^ codeword[499] ^ codeword[501] ^ codeword[504] ^ codeword[507] ^ codeword[508] ^ codeword[510] ^ codeword[511] ^ codeword[513] ^ codeword[515] ^ codeword[517] ^ codeword[519] ^ codeword[521] ^ codeword[524] ^ codeword[527] ^ codeword[529] ^ codeword[531] ^ codeword[534] ^ codeword[538] ^ codeword[542] ^ codeword[543] ^ codeword[545] ^ codeword[546] ^ codeword[548] ^ codeword[550] ^ codeword[552] ^ codeword[554] ^ codeword[556] ^ codeword[559] ^ codeword[562] ^ codeword[564] ^ codeword[566] ^ codeword[569] ^ codeword[573] ^ codeword[577] ^ codeword[579] ^ codeword[581] ^ codeword[584] ^ codeword[588] ^ codeword[593] ^ codeword[598] ^ codeword[599] ^ codeword[601] ^ codeword[602] ^ codeword[604] ^ codeword[606] ^ codeword[608] ^ codeword[610] ^ codeword[612] ^ codeword[615] ^ codeword[618] ^ codeword[620] ^ codeword[622] ^ codeword[625] ^ codeword[629] ^ codeword[633] ^ codeword[635] ^ codeword[637] ^ codeword[640] ^ codeword[644] ^ codeword[649] ^ codeword[654] ^ codeword[656] ^ codeword[658] ^ codeword[661] ^ codeword[665] ^ codeword[670] ^ codeword[676] ^ codeword[682] ^ codeword[683] ^ codeword[684] ^ codeword[686] ^ codeword[687] ^ codeword[688] ^ codeword[690] ^ codeword[691] ^ codeword[693] ^ codeword[695] ^ codeword[697] ^ codeword[698] ^ codeword[700] ^ codeword[701] ^ codeword[703] ^ codeword[705] ^ codeword[707] ^ codeword[709] ^ codeword[711] ^ codeword[714] ^ codeword[717] ^ codeword[718] ^ codeword[720] ^ codeword[721] ^ codeword[723] ^ codeword[725] ^ codeword[727] ^ codeword[729] ^ codeword[731] ^ codeword[734] ^ codeword[737] ^ codeword[739] ^ codeword[741] ^ codeword[744] ^ codeword[748] ^ codeword[752] ^ codeword[753] ^ codeword[755] ^ codeword[756] ^ codeword[758] ^ codeword[760] ^ codeword[762] ^ codeword[764] ^ codeword[766] ^ codeword[769] ^ codeword[772] ^ codeword[774] ^ codeword[776] ^ codeword[779] ^ codeword[783] ^ codeword[787] ^ codeword[789] ^ codeword[791] ^ codeword[794] ^ codeword[798] ^ codeword[803] ^ codeword[808] ^ codeword[809] ^ codeword[811] ^ codeword[812] ^ codeword[814] ^ codeword[816] ^ codeword[818] ^ codeword[820] ^ codeword[822] ^ codeword[825] ^ codeword[828] ^ codeword[830] ^ codeword[832] ^ codeword[835] ^ codeword[839] ^ codeword[843] ^ codeword[845] ^ codeword[847] ^ codeword[850] ^ codeword[854] ^ codeword[859] ^ codeword[864] ^ codeword[866] ^ codeword[868] ^ codeword[871] ^ codeword[875] ^ codeword[880] ^ codeword[886] ^ codeword[892] ^ codeword[893] ^ codeword[895] ^ codeword[896] ^ codeword[898] ^ codeword[900] ^ codeword[902] ^ codeword[904] ^ codeword[906] ^ codeword[909] ^ codeword[912] ^ codeword[914] ^ codeword[916] ^ codeword[919] ^ codeword[923] ^ codeword[927] ^ codeword[929] ^ codeword[931] ^ codeword[934] ^ codeword[938] ^ codeword[943] ^ codeword[948] ^ codeword[950] ^ codeword[952] ^ codeword[955] ^ codeword[959] ^ codeword[964] ^ codeword[970] ^ codeword[976] ^ codeword[978] ^ codeword[980] ^ codeword[983] ^ codeword[987] ^ codeword[992] ^ codeword[998] ^ codeword[1005] ^ codeword[1012] ^ codeword[1013] ^ codeword[1014] ^ codeword[1015] ^ codeword[1016] ^ codeword[1017] ^ codeword[1019] ^ codeword[1020] ^ codeword[1021] ^ codeword[1022] ^ codeword[1023] ^ codeword[1034];
    assign syndrome[11] = codeword[0] ^ codeword[1] ^ codeword[2] ^ codeword[4] ^ codeword[5] ^ codeword[7] ^ codeword[10] ^ codeword[11] ^ codeword[13] ^ codeword[16] ^ codeword[20] ^ codeword[21] ^ codeword[23] ^ codeword[26] ^ codeword[30] ^ codeword[35] ^ codeword[36] ^ codeword[38] ^ codeword[41] ^ codeword[45] ^ codeword[50] ^ codeword[56] ^ codeword[57] ^ codeword[59] ^ codeword[62] ^ codeword[66] ^ codeword[71] ^ codeword[77] ^ codeword[84] ^ codeword[85] ^ codeword[87] ^ codeword[90] ^ codeword[94] ^ codeword[99] ^ codeword[105] ^ codeword[112] ^ codeword[120] ^ codeword[121] ^ codeword[123] ^ codeword[126] ^ codeword[130] ^ codeword[135] ^ codeword[141] ^ codeword[148] ^ codeword[156] ^ codeword[165] ^ codeword[166] ^ codeword[168] ^ codeword[171] ^ codeword[175] ^ codeword[180] ^ codeword[186] ^ codeword[193] ^ codeword[201] ^ codeword[210] ^ codeword[220] ^ codeword[221] ^ codeword[222] ^ codeword[223] ^ codeword[224] ^ codeword[226] ^ codeword[227] ^ codeword[228] ^ codeword[229] ^ codeword[231] ^ codeword[232] ^ codeword[233] ^ codeword[235] ^ codeword[236] ^ codeword[238] ^ codeword[241] ^ codeword[242] ^ codeword[243] ^ codeword[244] ^ codeword[246] ^ codeword[247] ^ codeword[248] ^ codeword[250] ^ codeword[251] ^ codeword[253] ^ codeword[256] ^ codeword[257] ^ codeword[258] ^ codeword[260] ^ codeword[261] ^ codeword[263] ^ codeword[266] ^ codeword[267] ^ codeword[269] ^ codeword[272] ^ codeword[276] ^ codeword[277] ^ codeword[278] ^ codeword[279] ^ codeword[281] ^ codeword[282] ^ codeword[283] ^ codeword[285] ^ codeword[286] ^ codeword[288] ^ codeword[291] ^ codeword[292] ^ codeword[293] ^ codeword[295] ^ codeword[296] ^ codeword[298] ^ codeword[301] ^ codeword[302] ^ codeword[304] ^ codeword[307] ^ codeword[311] ^ codeword[312] ^ codeword[313] ^ codeword[315] ^ codeword[316] ^ codeword[318] ^ codeword[321] ^ codeword[322] ^ codeword[324] ^ codeword[327] ^ codeword[331] ^ codeword[332] ^ codeword[334] ^ codeword[337] ^ codeword[341] ^ codeword[346] ^ codeword[347] ^ codeword[348] ^ codeword[349] ^ codeword[351] ^ codeword[352] ^ codeword[353] ^ codeword[355] ^ codeword[356] ^ codeword[358] ^ codeword[361] ^ codeword[362] ^ codeword[363] ^ codeword[365] ^ codeword[366] ^ codeword[368] ^ codeword[371] ^ codeword[372] ^ codeword[374] ^ codeword[377] ^ codeword[381] ^ codeword[382] ^ codeword[383] ^ codeword[385] ^ codeword[386] ^ codeword[388] ^ codeword[391] ^ codeword[392] ^ codeword[394] ^ codeword[397] ^ codeword[401] ^ codeword[402] ^ codeword[404] ^ codeword[407] ^ codeword[411] ^ codeword[416] ^ codeword[417] ^ codeword[418] ^ codeword[420] ^ codeword[421] ^ codeword[423] ^ codeword[426] ^ codeword[427] ^ codeword[429] ^ codeword[432] ^ codeword[436] ^ codeword[437] ^ codeword[439] ^ codeword[442] ^ codeword[446] ^ codeword[451] ^ codeword[452] ^ codeword[454] ^ codeword[457] ^ codeword[461] ^ codeword[466] ^ codeword[472] ^ codeword[473] ^ codeword[474] ^ codeword[475] ^ codeword[477] ^ codeword[478] ^ codeword[479] ^ codeword[481] ^ codeword[482] ^ codeword[484] ^ codeword[487] ^ codeword[488] ^ codeword[489] ^ codeword[491] ^ codeword[492] ^ codeword[494] ^ codeword[497] ^ codeword[498] ^ codeword[500] ^ codeword[503] ^ codeword[507] ^ codeword[508] ^ codeword[509] ^ codeword[511] ^ codeword[512] ^ codeword[514] ^ codeword[517] ^ codeword[518] ^ codeword[520] ^ codeword[523] ^ codeword[527] ^ codeword[528] ^ codeword[530] ^ codeword[533] ^ codeword[537] ^ codeword[542] ^ codeword[543] ^ codeword[544] ^ codeword[546] ^ codeword[547] ^ codeword[549] ^ codeword[552] ^ codeword[553] ^ codeword[555] ^ codeword[558] ^ codeword[562] ^ codeword[563] ^ codeword[565] ^ codeword[568] ^ codeword[572] ^ codeword[577] ^ codeword[578] ^ codeword[580] ^ codeword[583] ^ codeword[587] ^ codeword[592] ^ codeword[598] ^ codeword[599] ^ codeword[600] ^ codeword[602] ^ codeword[603] ^ codeword[605] ^ codeword[608] ^ codeword[609] ^ codeword[611] ^ codeword[614] ^ codeword[618] ^ codeword[619] ^ codeword[621] ^ codeword[624] ^ codeword[628] ^ codeword[633] ^ codeword[634] ^ codeword[636] ^ codeword[639] ^ codeword[643] ^ codeword[648] ^ codeword[654] ^ codeword[655] ^ codeword[657] ^ codeword[660] ^ codeword[664] ^ codeword[669] ^ codeword[675] ^ codeword[682] ^ codeword[683] ^ codeword[684] ^ codeword[685] ^ codeword[687] ^ codeword[688] ^ codeword[689] ^ codeword[691] ^ codeword[692] ^ codeword[694] ^ codeword[697] ^ codeword[698] ^ codeword[699] ^ codeword[701] ^ codeword[702] ^ codeword[704] ^ codeword[707] ^ codeword[708] ^ codeword[710] ^ codeword[713] ^ codeword[717] ^ codeword[718] ^ codeword[719] ^ codeword[721] ^ codeword[722] ^ codeword[724] ^ codeword[727] ^ codeword[728] ^ codeword[730] ^ codeword[733] ^ codeword[737] ^ codeword[738] ^ codeword[740] ^ codeword[743] ^ codeword[747] ^ codeword[752] ^ codeword[753] ^ codeword[754] ^ codeword[756] ^ codeword[757] ^ codeword[759] ^ codeword[762] ^ codeword[763] ^ codeword[765] ^ codeword[768] ^ codeword[772] ^ codeword[773] ^ codeword[775] ^ codeword[778] ^ codeword[782] ^ codeword[787] ^ codeword[788] ^ codeword[790] ^ codeword[793] ^ codeword[797] ^ codeword[802] ^ codeword[808] ^ codeword[809] ^ codeword[810] ^ codeword[812] ^ codeword[813] ^ codeword[815] ^ codeword[818] ^ codeword[819] ^ codeword[821] ^ codeword[824] ^ codeword[828] ^ codeword[829] ^ codeword[831] ^ codeword[834] ^ codeword[838] ^ codeword[843] ^ codeword[844] ^ codeword[846] ^ codeword[849] ^ codeword[853] ^ codeword[858] ^ codeword[864] ^ codeword[865] ^ codeword[867] ^ codeword[870] ^ codeword[874] ^ codeword[879] ^ codeword[885] ^ codeword[892] ^ codeword[893] ^ codeword[894] ^ codeword[896] ^ codeword[897] ^ codeword[899] ^ codeword[902] ^ codeword[903] ^ codeword[905] ^ codeword[908] ^ codeword[912] ^ codeword[913] ^ codeword[915] ^ codeword[918] ^ codeword[922] ^ codeword[927] ^ codeword[928] ^ codeword[930] ^ codeword[933] ^ codeword[937] ^ codeword[942] ^ codeword[948] ^ codeword[949] ^ codeword[951] ^ codeword[954] ^ codeword[958] ^ codeword[963] ^ codeword[969] ^ codeword[976] ^ codeword[977] ^ codeword[979] ^ codeword[982] ^ codeword[986] ^ codeword[991] ^ codeword[997] ^ codeword[1004] ^ codeword[1012] ^ codeword[1013] ^ codeword[1014] ^ codeword[1015] ^ codeword[1016] ^ codeword[1017] ^ codeword[1018] ^ codeword[1020] ^ codeword[1021] ^ codeword[1022] ^ codeword[1023] ^ codeword[1035];
    assign parity_check_matrix[0] = 12'b000000000111;
    assign parity_check_matrix[1] = 12'b000000001011;
    assign parity_check_matrix[2] = 12'b000000001101;
    assign parity_check_matrix[3] = 12'b000000001110;
    assign parity_check_matrix[4] = 12'b000000010011;
    assign parity_check_matrix[5] = 12'b000000010101;
    assign parity_check_matrix[6] = 12'b000000010110;
    assign parity_check_matrix[7] = 12'b000000011001;
    assign parity_check_matrix[8] = 12'b000000011010;
    assign parity_check_matrix[9] = 12'b000000011100;
    assign parity_check_matrix[10] = 12'b000000100011;
    assign parity_check_matrix[11] = 12'b000000100101;
    assign parity_check_matrix[12] = 12'b000000100110;
    assign parity_check_matrix[13] = 12'b000000101001;
    assign parity_check_matrix[14] = 12'b000000101010;
    assign parity_check_matrix[15] = 12'b000000101100;
    assign parity_check_matrix[16] = 12'b000000110001;
    assign parity_check_matrix[17] = 12'b000000110010;
    assign parity_check_matrix[18] = 12'b000000110100;
    assign parity_check_matrix[19] = 12'b000000111000;
    assign parity_check_matrix[20] = 12'b000001000011;
    assign parity_check_matrix[21] = 12'b000001000101;
    assign parity_check_matrix[22] = 12'b000001000110;
    assign parity_check_matrix[23] = 12'b000001001001;
    assign parity_check_matrix[24] = 12'b000001001010;
    assign parity_check_matrix[25] = 12'b000001001100;
    assign parity_check_matrix[26] = 12'b000001010001;
    assign parity_check_matrix[27] = 12'b000001010010;
    assign parity_check_matrix[28] = 12'b000001010100;
    assign parity_check_matrix[29] = 12'b000001011000;
    assign parity_check_matrix[30] = 12'b000001100001;
    assign parity_check_matrix[31] = 12'b000001100010;
    assign parity_check_matrix[32] = 12'b000001100100;
    assign parity_check_matrix[33] = 12'b000001101000;
    assign parity_check_matrix[34] = 12'b000001110000;
    assign parity_check_matrix[35] = 12'b000010000011;
    assign parity_check_matrix[36] = 12'b000010000101;
    assign parity_check_matrix[37] = 12'b000010000110;
    assign parity_check_matrix[38] = 12'b000010001001;
    assign parity_check_matrix[39] = 12'b000010001010;
    assign parity_check_matrix[40] = 12'b000010001100;
    assign parity_check_matrix[41] = 12'b000010010001;
    assign parity_check_matrix[42] = 12'b000010010010;
    assign parity_check_matrix[43] = 12'b000010010100;
    assign parity_check_matrix[44] = 12'b000010011000;
    assign parity_check_matrix[45] = 12'b000010100001;
    assign parity_check_matrix[46] = 12'b000010100010;
    assign parity_check_matrix[47] = 12'b000010100100;
    assign parity_check_matrix[48] = 12'b000010101000;
    assign parity_check_matrix[49] = 12'b000010110000;
    assign parity_check_matrix[50] = 12'b000011000001;
    assign parity_check_matrix[51] = 12'b000011000010;
    assign parity_check_matrix[52] = 12'b000011000100;
    assign parity_check_matrix[53] = 12'b000011001000;
    assign parity_check_matrix[54] = 12'b000011010000;
    assign parity_check_matrix[55] = 12'b000011100000;
    assign parity_check_matrix[56] = 12'b000100000011;
    assign parity_check_matrix[57] = 12'b000100000101;
    assign parity_check_matrix[58] = 12'b000100000110;
    assign parity_check_matrix[59] = 12'b000100001001;
    assign parity_check_matrix[60] = 12'b000100001010;
    assign parity_check_matrix[61] = 12'b000100001100;
    assign parity_check_matrix[62] = 12'b000100010001;
    assign parity_check_matrix[63] = 12'b000100010010;
    assign parity_check_matrix[64] = 12'b000100010100;
    assign parity_check_matrix[65] = 12'b000100011000;
    assign parity_check_matrix[66] = 12'b000100100001;
    assign parity_check_matrix[67] = 12'b000100100010;
    assign parity_check_matrix[68] = 12'b000100100100;
    assign parity_check_matrix[69] = 12'b000100101000;
    assign parity_check_matrix[70] = 12'b000100110000;
    assign parity_check_matrix[71] = 12'b000101000001;
    assign parity_check_matrix[72] = 12'b000101000010;
    assign parity_check_matrix[73] = 12'b000101000100;
    assign parity_check_matrix[74] = 12'b000101001000;
    assign parity_check_matrix[75] = 12'b000101010000;
    assign parity_check_matrix[76] = 12'b000101100000;
    assign parity_check_matrix[77] = 12'b000110000001;
    assign parity_check_matrix[78] = 12'b000110000010;
    assign parity_check_matrix[79] = 12'b000110000100;
    assign parity_check_matrix[80] = 12'b000110001000;
    assign parity_check_matrix[81] = 12'b000110010000;
    assign parity_check_matrix[82] = 12'b000110100000;
    assign parity_check_matrix[83] = 12'b000111000000;
    assign parity_check_matrix[84] = 12'b001000000011;
    assign parity_check_matrix[85] = 12'b001000000101;
    assign parity_check_matrix[86] = 12'b001000000110;
    assign parity_check_matrix[87] = 12'b001000001001;
    assign parity_check_matrix[88] = 12'b001000001010;
    assign parity_check_matrix[89] = 12'b001000001100;
    assign parity_check_matrix[90] = 12'b001000010001;
    assign parity_check_matrix[91] = 12'b001000010010;
    assign parity_check_matrix[92] = 12'b001000010100;
    assign parity_check_matrix[93] = 12'b001000011000;
    assign parity_check_matrix[94] = 12'b001000100001;
    assign parity_check_matrix[95] = 12'b001000100010;
    assign parity_check_matrix[96] = 12'b001000100100;
    assign parity_check_matrix[97] = 12'b001000101000;
    assign parity_check_matrix[98] = 12'b001000110000;
    assign parity_check_matrix[99] = 12'b001001000001;
    assign parity_check_matrix[100] = 12'b001001000010;
    assign parity_check_matrix[101] = 12'b001001000100;
    assign parity_check_matrix[102] = 12'b001001001000;
    assign parity_check_matrix[103] = 12'b001001010000;
    assign parity_check_matrix[104] = 12'b001001100000;
    assign parity_check_matrix[105] = 12'b001010000001;
    assign parity_check_matrix[106] = 12'b001010000010;
    assign parity_check_matrix[107] = 12'b001010000100;
    assign parity_check_matrix[108] = 12'b001010001000;
    assign parity_check_matrix[109] = 12'b001010010000;
    assign parity_check_matrix[110] = 12'b001010100000;
    assign parity_check_matrix[111] = 12'b001011000000;
    assign parity_check_matrix[112] = 12'b001100000001;
    assign parity_check_matrix[113] = 12'b001100000010;
    assign parity_check_matrix[114] = 12'b001100000100;
    assign parity_check_matrix[115] = 12'b001100001000;
    assign parity_check_matrix[116] = 12'b001100010000;
    assign parity_check_matrix[117] = 12'b001100100000;
    assign parity_check_matrix[118] = 12'b001101000000;
    assign parity_check_matrix[119] = 12'b001110000000;
    assign parity_check_matrix[120] = 12'b010000000011;
    assign parity_check_matrix[121] = 12'b010000000101;
    assign parity_check_matrix[122] = 12'b010000000110;
    assign parity_check_matrix[123] = 12'b010000001001;
    assign parity_check_matrix[124] = 12'b010000001010;
    assign parity_check_matrix[125] = 12'b010000001100;
    assign parity_check_matrix[126] = 12'b010000010001;
    assign parity_check_matrix[127] = 12'b010000010010;
    assign parity_check_matrix[128] = 12'b010000010100;
    assign parity_check_matrix[129] = 12'b010000011000;
    assign parity_check_matrix[130] = 12'b010000100001;
    assign parity_check_matrix[131] = 12'b010000100010;
    assign parity_check_matrix[132] = 12'b010000100100;
    assign parity_check_matrix[133] = 12'b010000101000;
    assign parity_check_matrix[134] = 12'b010000110000;
    assign parity_check_matrix[135] = 12'b010001000001;
    assign parity_check_matrix[136] = 12'b010001000010;
    assign parity_check_matrix[137] = 12'b010001000100;
    assign parity_check_matrix[138] = 12'b010001001000;
    assign parity_check_matrix[139] = 12'b010001010000;
    assign parity_check_matrix[140] = 12'b010001100000;
    assign parity_check_matrix[141] = 12'b010010000001;
    assign parity_check_matrix[142] = 12'b010010000010;
    assign parity_check_matrix[143] = 12'b010010000100;
    assign parity_check_matrix[144] = 12'b010010001000;
    assign parity_check_matrix[145] = 12'b010010010000;
    assign parity_check_matrix[146] = 12'b010010100000;
    assign parity_check_matrix[147] = 12'b010011000000;
    assign parity_check_matrix[148] = 12'b010100000001;
    assign parity_check_matrix[149] = 12'b010100000010;
    assign parity_check_matrix[150] = 12'b010100000100;
    assign parity_check_matrix[151] = 12'b010100001000;
    assign parity_check_matrix[152] = 12'b010100010000;
    assign parity_check_matrix[153] = 12'b010100100000;
    assign parity_check_matrix[154] = 12'b010101000000;
    assign parity_check_matrix[155] = 12'b010110000000;
    assign parity_check_matrix[156] = 12'b011000000001;
    assign parity_check_matrix[157] = 12'b011000000010;
    assign parity_check_matrix[158] = 12'b011000000100;
    assign parity_check_matrix[159] = 12'b011000001000;
    assign parity_check_matrix[160] = 12'b011000010000;
    assign parity_check_matrix[161] = 12'b011000100000;
    assign parity_check_matrix[162] = 12'b011001000000;
    assign parity_check_matrix[163] = 12'b011010000000;
    assign parity_check_matrix[164] = 12'b011100000000;
    assign parity_check_matrix[165] = 12'b100000000011;
    assign parity_check_matrix[166] = 12'b100000000101;
    assign parity_check_matrix[167] = 12'b100000000110;
    assign parity_check_matrix[168] = 12'b100000001001;
    assign parity_check_matrix[169] = 12'b100000001010;
    assign parity_check_matrix[170] = 12'b100000001100;
    assign parity_check_matrix[171] = 12'b100000010001;
    assign parity_check_matrix[172] = 12'b100000010010;
    assign parity_check_matrix[173] = 12'b100000010100;
    assign parity_check_matrix[174] = 12'b100000011000;
    assign parity_check_matrix[175] = 12'b100000100001;
    assign parity_check_matrix[176] = 12'b100000100010;
    assign parity_check_matrix[177] = 12'b100000100100;
    assign parity_check_matrix[178] = 12'b100000101000;
    assign parity_check_matrix[179] = 12'b100000110000;
    assign parity_check_matrix[180] = 12'b100001000001;
    assign parity_check_matrix[181] = 12'b100001000010;
    assign parity_check_matrix[182] = 12'b100001000100;
    assign parity_check_matrix[183] = 12'b100001001000;
    assign parity_check_matrix[184] = 12'b100001010000;
    assign parity_check_matrix[185] = 12'b100001100000;
    assign parity_check_matrix[186] = 12'b100010000001;
    assign parity_check_matrix[187] = 12'b100010000010;
    assign parity_check_matrix[188] = 12'b100010000100;
    assign parity_check_matrix[189] = 12'b100010001000;
    assign parity_check_matrix[190] = 12'b100010010000;
    assign parity_check_matrix[191] = 12'b100010100000;
    assign parity_check_matrix[192] = 12'b100011000000;
    assign parity_check_matrix[193] = 12'b100100000001;
    assign parity_check_matrix[194] = 12'b100100000010;
    assign parity_check_matrix[195] = 12'b100100000100;
    assign parity_check_matrix[196] = 12'b100100001000;
    assign parity_check_matrix[197] = 12'b100100010000;
    assign parity_check_matrix[198] = 12'b100100100000;
    assign parity_check_matrix[199] = 12'b100101000000;
    assign parity_check_matrix[200] = 12'b100110000000;
    assign parity_check_matrix[201] = 12'b101000000001;
    assign parity_check_matrix[202] = 12'b101000000010;
    assign parity_check_matrix[203] = 12'b101000000100;
    assign parity_check_matrix[204] = 12'b101000001000;
    assign parity_check_matrix[205] = 12'b101000010000;
    assign parity_check_matrix[206] = 12'b101000100000;
    assign parity_check_matrix[207] = 12'b101001000000;
    assign parity_check_matrix[208] = 12'b101010000000;
    assign parity_check_matrix[209] = 12'b101100000000;
    assign parity_check_matrix[210] = 12'b110000000001;
    assign parity_check_matrix[211] = 12'b110000000010;
    assign parity_check_matrix[212] = 12'b110000000100;
    assign parity_check_matrix[213] = 12'b110000001000;
    assign parity_check_matrix[214] = 12'b110000010000;
    assign parity_check_matrix[215] = 12'b110000100000;
    assign parity_check_matrix[216] = 12'b110001000000;
    assign parity_check_matrix[217] = 12'b110010000000;
    assign parity_check_matrix[218] = 12'b110100000000;
    assign parity_check_matrix[219] = 12'b111000000000;
    assign parity_check_matrix[220] = 12'b000000011111;
    assign parity_check_matrix[221] = 12'b000000101111;
    assign parity_check_matrix[222] = 12'b000000110111;
    assign parity_check_matrix[223] = 12'b000000111011;
    assign parity_check_matrix[224] = 12'b000000111101;
    assign parity_check_matrix[225] = 12'b000000111110;
    assign parity_check_matrix[226] = 12'b000001001111;
    assign parity_check_matrix[227] = 12'b000001010111;
    assign parity_check_matrix[228] = 12'b000001011011;
    assign parity_check_matrix[229] = 12'b000001011101;
    assign parity_check_matrix[230] = 12'b000001011110;
    assign parity_check_matrix[231] = 12'b000001100111;
    assign parity_check_matrix[232] = 12'b000001101011;
    assign parity_check_matrix[233] = 12'b000001101101;
    assign parity_check_matrix[234] = 12'b000001101110;
    assign parity_check_matrix[235] = 12'b000001110011;
    assign parity_check_matrix[236] = 12'b000001110101;
    assign parity_check_matrix[237] = 12'b000001110110;
    assign parity_check_matrix[238] = 12'b000001111001;
    assign parity_check_matrix[239] = 12'b000001111010;
    assign parity_check_matrix[240] = 12'b000001111100;
    assign parity_check_matrix[241] = 12'b000010001111;
    assign parity_check_matrix[242] = 12'b000010010111;
    assign parity_check_matrix[243] = 12'b000010011011;
    assign parity_check_matrix[244] = 12'b000010011101;
    assign parity_check_matrix[245] = 12'b000010011110;
    assign parity_check_matrix[246] = 12'b000010100111;
    assign parity_check_matrix[247] = 12'b000010101011;
    assign parity_check_matrix[248] = 12'b000010101101;
    assign parity_check_matrix[249] = 12'b000010101110;
    assign parity_check_matrix[250] = 12'b000010110011;
    assign parity_check_matrix[251] = 12'b000010110101;
    assign parity_check_matrix[252] = 12'b000010110110;
    assign parity_check_matrix[253] = 12'b000010111001;
    assign parity_check_matrix[254] = 12'b000010111010;
    assign parity_check_matrix[255] = 12'b000010111100;
    assign parity_check_matrix[256] = 12'b000011000111;
    assign parity_check_matrix[257] = 12'b000011001011;
    assign parity_check_matrix[258] = 12'b000011001101;
    assign parity_check_matrix[259] = 12'b000011001110;
    assign parity_check_matrix[260] = 12'b000011010011;
    assign parity_check_matrix[261] = 12'b000011010101;
    assign parity_check_matrix[262] = 12'b000011010110;
    assign parity_check_matrix[263] = 12'b000011011001;
    assign parity_check_matrix[264] = 12'b000011011010;
    assign parity_check_matrix[265] = 12'b000011011100;
    assign parity_check_matrix[266] = 12'b000011100011;
    assign parity_check_matrix[267] = 12'b000011100101;
    assign parity_check_matrix[268] = 12'b000011100110;
    assign parity_check_matrix[269] = 12'b000011101001;
    assign parity_check_matrix[270] = 12'b000011101010;
    assign parity_check_matrix[271] = 12'b000011101100;
    assign parity_check_matrix[272] = 12'b000011110001;
    assign parity_check_matrix[273] = 12'b000011110010;
    assign parity_check_matrix[274] = 12'b000011110100;
    assign parity_check_matrix[275] = 12'b000011111000;
    assign parity_check_matrix[276] = 12'b000100001111;
    assign parity_check_matrix[277] = 12'b000100010111;
    assign parity_check_matrix[278] = 12'b000100011011;
    assign parity_check_matrix[279] = 12'b000100011101;
    assign parity_check_matrix[280] = 12'b000100011110;
    assign parity_check_matrix[281] = 12'b000100100111;
    assign parity_check_matrix[282] = 12'b000100101011;
    assign parity_check_matrix[283] = 12'b000100101101;
    assign parity_check_matrix[284] = 12'b000100101110;
    assign parity_check_matrix[285] = 12'b000100110011;
    assign parity_check_matrix[286] = 12'b000100110101;
    assign parity_check_matrix[287] = 12'b000100110110;
    assign parity_check_matrix[288] = 12'b000100111001;
    assign parity_check_matrix[289] = 12'b000100111010;
    assign parity_check_matrix[290] = 12'b000100111100;
    assign parity_check_matrix[291] = 12'b000101000111;
    assign parity_check_matrix[292] = 12'b000101001011;
    assign parity_check_matrix[293] = 12'b000101001101;
    assign parity_check_matrix[294] = 12'b000101001110;
    assign parity_check_matrix[295] = 12'b000101010011;
    assign parity_check_matrix[296] = 12'b000101010101;
    assign parity_check_matrix[297] = 12'b000101010110;
    assign parity_check_matrix[298] = 12'b000101011001;
    assign parity_check_matrix[299] = 12'b000101011010;
    assign parity_check_matrix[300] = 12'b000101011100;
    assign parity_check_matrix[301] = 12'b000101100011;
    assign parity_check_matrix[302] = 12'b000101100101;
    assign parity_check_matrix[303] = 12'b000101100110;
    assign parity_check_matrix[304] = 12'b000101101001;
    assign parity_check_matrix[305] = 12'b000101101010;
    assign parity_check_matrix[306] = 12'b000101101100;
    assign parity_check_matrix[307] = 12'b000101110001;
    assign parity_check_matrix[308] = 12'b000101110010;
    assign parity_check_matrix[309] = 12'b000101110100;
    assign parity_check_matrix[310] = 12'b000101111000;
    assign parity_check_matrix[311] = 12'b000110000111;
    assign parity_check_matrix[312] = 12'b000110001011;
    assign parity_check_matrix[313] = 12'b000110001101;
    assign parity_check_matrix[314] = 12'b000110001110;
    assign parity_check_matrix[315] = 12'b000110010011;
    assign parity_check_matrix[316] = 12'b000110010101;
    assign parity_check_matrix[317] = 12'b000110010110;
    assign parity_check_matrix[318] = 12'b000110011001;
    assign parity_check_matrix[319] = 12'b000110011010;
    assign parity_check_matrix[320] = 12'b000110011100;
    assign parity_check_matrix[321] = 12'b000110100011;
    assign parity_check_matrix[322] = 12'b000110100101;
    assign parity_check_matrix[323] = 12'b000110100110;
    assign parity_check_matrix[324] = 12'b000110101001;
    assign parity_check_matrix[325] = 12'b000110101010;
    assign parity_check_matrix[326] = 12'b000110101100;
    assign parity_check_matrix[327] = 12'b000110110001;
    assign parity_check_matrix[328] = 12'b000110110010;
    assign parity_check_matrix[329] = 12'b000110110100;
    assign parity_check_matrix[330] = 12'b000110111000;
    assign parity_check_matrix[331] = 12'b000111000011;
    assign parity_check_matrix[332] = 12'b000111000101;
    assign parity_check_matrix[333] = 12'b000111000110;
    assign parity_check_matrix[334] = 12'b000111001001;
    assign parity_check_matrix[335] = 12'b000111001010;
    assign parity_check_matrix[336] = 12'b000111001100;
    assign parity_check_matrix[337] = 12'b000111010001;
    assign parity_check_matrix[338] = 12'b000111010010;
    assign parity_check_matrix[339] = 12'b000111010100;
    assign parity_check_matrix[340] = 12'b000111011000;
    assign parity_check_matrix[341] = 12'b000111100001;
    assign parity_check_matrix[342] = 12'b000111100010;
    assign parity_check_matrix[343] = 12'b000111100100;
    assign parity_check_matrix[344] = 12'b000111101000;
    assign parity_check_matrix[345] = 12'b000111110000;
    assign parity_check_matrix[346] = 12'b001000001111;
    assign parity_check_matrix[347] = 12'b001000010111;
    assign parity_check_matrix[348] = 12'b001000011011;
    assign parity_check_matrix[349] = 12'b001000011101;
    assign parity_check_matrix[350] = 12'b001000011110;
    assign parity_check_matrix[351] = 12'b001000100111;
    assign parity_check_matrix[352] = 12'b001000101011;
    assign parity_check_matrix[353] = 12'b001000101101;
    assign parity_check_matrix[354] = 12'b001000101110;
    assign parity_check_matrix[355] = 12'b001000110011;
    assign parity_check_matrix[356] = 12'b001000110101;
    assign parity_check_matrix[357] = 12'b001000110110;
    assign parity_check_matrix[358] = 12'b001000111001;
    assign parity_check_matrix[359] = 12'b001000111010;
    assign parity_check_matrix[360] = 12'b001000111100;
    assign parity_check_matrix[361] = 12'b001001000111;
    assign parity_check_matrix[362] = 12'b001001001011;
    assign parity_check_matrix[363] = 12'b001001001101;
    assign parity_check_matrix[364] = 12'b001001001110;
    assign parity_check_matrix[365] = 12'b001001010011;
    assign parity_check_matrix[366] = 12'b001001010101;
    assign parity_check_matrix[367] = 12'b001001010110;
    assign parity_check_matrix[368] = 12'b001001011001;
    assign parity_check_matrix[369] = 12'b001001011010;
    assign parity_check_matrix[370] = 12'b001001011100;
    assign parity_check_matrix[371] = 12'b001001100011;
    assign parity_check_matrix[372] = 12'b001001100101;
    assign parity_check_matrix[373] = 12'b001001100110;
    assign parity_check_matrix[374] = 12'b001001101001;
    assign parity_check_matrix[375] = 12'b001001101010;
    assign parity_check_matrix[376] = 12'b001001101100;
    assign parity_check_matrix[377] = 12'b001001110001;
    assign parity_check_matrix[378] = 12'b001001110010;
    assign parity_check_matrix[379] = 12'b001001110100;
    assign parity_check_matrix[380] = 12'b001001111000;
    assign parity_check_matrix[381] = 12'b001010000111;
    assign parity_check_matrix[382] = 12'b001010001011;
    assign parity_check_matrix[383] = 12'b001010001101;
    assign parity_check_matrix[384] = 12'b001010001110;
    assign parity_check_matrix[385] = 12'b001010010011;
    assign parity_check_matrix[386] = 12'b001010010101;
    assign parity_check_matrix[387] = 12'b001010010110;
    assign parity_check_matrix[388] = 12'b001010011001;
    assign parity_check_matrix[389] = 12'b001010011010;
    assign parity_check_matrix[390] = 12'b001010011100;
    assign parity_check_matrix[391] = 12'b001010100011;
    assign parity_check_matrix[392] = 12'b001010100101;
    assign parity_check_matrix[393] = 12'b001010100110;
    assign parity_check_matrix[394] = 12'b001010101001;
    assign parity_check_matrix[395] = 12'b001010101010;
    assign parity_check_matrix[396] = 12'b001010101100;
    assign parity_check_matrix[397] = 12'b001010110001;
    assign parity_check_matrix[398] = 12'b001010110010;
    assign parity_check_matrix[399] = 12'b001010110100;
    assign parity_check_matrix[400] = 12'b001010111000;
    assign parity_check_matrix[401] = 12'b001011000011;
    assign parity_check_matrix[402] = 12'b001011000101;
    assign parity_check_matrix[403] = 12'b001011000110;
    assign parity_check_matrix[404] = 12'b001011001001;
    assign parity_check_matrix[405] = 12'b001011001010;
    assign parity_check_matrix[406] = 12'b001011001100;
    assign parity_check_matrix[407] = 12'b001011010001;
    assign parity_check_matrix[408] = 12'b001011010010;
    assign parity_check_matrix[409] = 12'b001011010100;
    assign parity_check_matrix[410] = 12'b001011011000;
    assign parity_check_matrix[411] = 12'b001011100001;
    assign parity_check_matrix[412] = 12'b001011100010;
    assign parity_check_matrix[413] = 12'b001011100100;
    assign parity_check_matrix[414] = 12'b001011101000;
    assign parity_check_matrix[415] = 12'b001011110000;
    assign parity_check_matrix[416] = 12'b001100000111;
    assign parity_check_matrix[417] = 12'b001100001011;
    assign parity_check_matrix[418] = 12'b001100001101;
    assign parity_check_matrix[419] = 12'b001100001110;
    assign parity_check_matrix[420] = 12'b001100010011;
    assign parity_check_matrix[421] = 12'b001100010101;
    assign parity_check_matrix[422] = 12'b001100010110;
    assign parity_check_matrix[423] = 12'b001100011001;
    assign parity_check_matrix[424] = 12'b001100011010;
    assign parity_check_matrix[425] = 12'b001100011100;
    assign parity_check_matrix[426] = 12'b001100100011;
    assign parity_check_matrix[427] = 12'b001100100101;
    assign parity_check_matrix[428] = 12'b001100100110;
    assign parity_check_matrix[429] = 12'b001100101001;
    assign parity_check_matrix[430] = 12'b001100101010;
    assign parity_check_matrix[431] = 12'b001100101100;
    assign parity_check_matrix[432] = 12'b001100110001;
    assign parity_check_matrix[433] = 12'b001100110010;
    assign parity_check_matrix[434] = 12'b001100110100;
    assign parity_check_matrix[435] = 12'b001100111000;
    assign parity_check_matrix[436] = 12'b001101000011;
    assign parity_check_matrix[437] = 12'b001101000101;
    assign parity_check_matrix[438] = 12'b001101000110;
    assign parity_check_matrix[439] = 12'b001101001001;
    assign parity_check_matrix[440] = 12'b001101001010;
    assign parity_check_matrix[441] = 12'b001101001100;
    assign parity_check_matrix[442] = 12'b001101010001;
    assign parity_check_matrix[443] = 12'b001101010010;
    assign parity_check_matrix[444] = 12'b001101010100;
    assign parity_check_matrix[445] = 12'b001101011000;
    assign parity_check_matrix[446] = 12'b001101100001;
    assign parity_check_matrix[447] = 12'b001101100010;
    assign parity_check_matrix[448] = 12'b001101100100;
    assign parity_check_matrix[449] = 12'b001101101000;
    assign parity_check_matrix[450] = 12'b001101110000;
    assign parity_check_matrix[451] = 12'b001110000011;
    assign parity_check_matrix[452] = 12'b001110000101;
    assign parity_check_matrix[453] = 12'b001110000110;
    assign parity_check_matrix[454] = 12'b001110001001;
    assign parity_check_matrix[455] = 12'b001110001010;
    assign parity_check_matrix[456] = 12'b001110001100;
    assign parity_check_matrix[457] = 12'b001110010001;
    assign parity_check_matrix[458] = 12'b001110010010;
    assign parity_check_matrix[459] = 12'b001110010100;
    assign parity_check_matrix[460] = 12'b001110011000;
    assign parity_check_matrix[461] = 12'b001110100001;
    assign parity_check_matrix[462] = 12'b001110100010;
    assign parity_check_matrix[463] = 12'b001110100100;
    assign parity_check_matrix[464] = 12'b001110101000;
    assign parity_check_matrix[465] = 12'b001110110000;
    assign parity_check_matrix[466] = 12'b001111000001;
    assign parity_check_matrix[467] = 12'b001111000010;
    assign parity_check_matrix[468] = 12'b001111000100;
    assign parity_check_matrix[469] = 12'b001111001000;
    assign parity_check_matrix[470] = 12'b001111010000;
    assign parity_check_matrix[471] = 12'b001111100000;
    assign parity_check_matrix[472] = 12'b010000001111;
    assign parity_check_matrix[473] = 12'b010000010111;
    assign parity_check_matrix[474] = 12'b010000011011;
    assign parity_check_matrix[475] = 12'b010000011101;
    assign parity_check_matrix[476] = 12'b010000011110;
    assign parity_check_matrix[477] = 12'b010000100111;
    assign parity_check_matrix[478] = 12'b010000101011;
    assign parity_check_matrix[479] = 12'b010000101101;
    assign parity_check_matrix[480] = 12'b010000101110;
    assign parity_check_matrix[481] = 12'b010000110011;
    assign parity_check_matrix[482] = 12'b010000110101;
    assign parity_check_matrix[483] = 12'b010000110110;
    assign parity_check_matrix[484] = 12'b010000111001;
    assign parity_check_matrix[485] = 12'b010000111010;
    assign parity_check_matrix[486] = 12'b010000111100;
    assign parity_check_matrix[487] = 12'b010001000111;
    assign parity_check_matrix[488] = 12'b010001001011;
    assign parity_check_matrix[489] = 12'b010001001101;
    assign parity_check_matrix[490] = 12'b010001001110;
    assign parity_check_matrix[491] = 12'b010001010011;
    assign parity_check_matrix[492] = 12'b010001010101;
    assign parity_check_matrix[493] = 12'b010001010110;
    assign parity_check_matrix[494] = 12'b010001011001;
    assign parity_check_matrix[495] = 12'b010001011010;
    assign parity_check_matrix[496] = 12'b010001011100;
    assign parity_check_matrix[497] = 12'b010001100011;
    assign parity_check_matrix[498] = 12'b010001100101;
    assign parity_check_matrix[499] = 12'b010001100110;
    assign parity_check_matrix[500] = 12'b010001101001;
    assign parity_check_matrix[501] = 12'b010001101010;
    assign parity_check_matrix[502] = 12'b010001101100;
    assign parity_check_matrix[503] = 12'b010001110001;
    assign parity_check_matrix[504] = 12'b010001110010;
    assign parity_check_matrix[505] = 12'b010001110100;
    assign parity_check_matrix[506] = 12'b010001111000;
    assign parity_check_matrix[507] = 12'b010010000111;
    assign parity_check_matrix[508] = 12'b010010001011;
    assign parity_check_matrix[509] = 12'b010010001101;
    assign parity_check_matrix[510] = 12'b010010001110;
    assign parity_check_matrix[511] = 12'b010010010011;
    assign parity_check_matrix[512] = 12'b010010010101;
    assign parity_check_matrix[513] = 12'b010010010110;
    assign parity_check_matrix[514] = 12'b010010011001;
    assign parity_check_matrix[515] = 12'b010010011010;
    assign parity_check_matrix[516] = 12'b010010011100;
    assign parity_check_matrix[517] = 12'b010010100011;
    assign parity_check_matrix[518] = 12'b010010100101;
    assign parity_check_matrix[519] = 12'b010010100110;
    assign parity_check_matrix[520] = 12'b010010101001;
    assign parity_check_matrix[521] = 12'b010010101010;
    assign parity_check_matrix[522] = 12'b010010101100;
    assign parity_check_matrix[523] = 12'b010010110001;
    assign parity_check_matrix[524] = 12'b010010110010;
    assign parity_check_matrix[525] = 12'b010010110100;
    assign parity_check_matrix[526] = 12'b010010111000;
    assign parity_check_matrix[527] = 12'b010011000011;
    assign parity_check_matrix[528] = 12'b010011000101;
    assign parity_check_matrix[529] = 12'b010011000110;
    assign parity_check_matrix[530] = 12'b010011001001;
    assign parity_check_matrix[531] = 12'b010011001010;
    assign parity_check_matrix[532] = 12'b010011001100;
    assign parity_check_matrix[533] = 12'b010011010001;
    assign parity_check_matrix[534] = 12'b010011010010;
    assign parity_check_matrix[535] = 12'b010011010100;
    assign parity_check_matrix[536] = 12'b010011011000;
    assign parity_check_matrix[537] = 12'b010011100001;
    assign parity_check_matrix[538] = 12'b010011100010;
    assign parity_check_matrix[539] = 12'b010011100100;
    assign parity_check_matrix[540] = 12'b010011101000;
    assign parity_check_matrix[541] = 12'b010011110000;
    assign parity_check_matrix[542] = 12'b010100000111;
    assign parity_check_matrix[543] = 12'b010100001011;
    assign parity_check_matrix[544] = 12'b010100001101;
    assign parity_check_matrix[545] = 12'b010100001110;
    assign parity_check_matrix[546] = 12'b010100010011;
    assign parity_check_matrix[547] = 12'b010100010101;
    assign parity_check_matrix[548] = 12'b010100010110;
    assign parity_check_matrix[549] = 12'b010100011001;
    assign parity_check_matrix[550] = 12'b010100011010;
    assign parity_check_matrix[551] = 12'b010100011100;
    assign parity_check_matrix[552] = 12'b010100100011;
    assign parity_check_matrix[553] = 12'b010100100101;
    assign parity_check_matrix[554] = 12'b010100100110;
    assign parity_check_matrix[555] = 12'b010100101001;
    assign parity_check_matrix[556] = 12'b010100101010;
    assign parity_check_matrix[557] = 12'b010100101100;
    assign parity_check_matrix[558] = 12'b010100110001;
    assign parity_check_matrix[559] = 12'b010100110010;
    assign parity_check_matrix[560] = 12'b010100110100;
    assign parity_check_matrix[561] = 12'b010100111000;
    assign parity_check_matrix[562] = 12'b010101000011;
    assign parity_check_matrix[563] = 12'b010101000101;
    assign parity_check_matrix[564] = 12'b010101000110;
    assign parity_check_matrix[565] = 12'b010101001001;
    assign parity_check_matrix[566] = 12'b010101001010;
    assign parity_check_matrix[567] = 12'b010101001100;
    assign parity_check_matrix[568] = 12'b010101010001;
    assign parity_check_matrix[569] = 12'b010101010010;
    assign parity_check_matrix[570] = 12'b010101010100;
    assign parity_check_matrix[571] = 12'b010101011000;
    assign parity_check_matrix[572] = 12'b010101100001;
    assign parity_check_matrix[573] = 12'b010101100010;
    assign parity_check_matrix[574] = 12'b010101100100;
    assign parity_check_matrix[575] = 12'b010101101000;
    assign parity_check_matrix[576] = 12'b010101110000;
    assign parity_check_matrix[577] = 12'b010110000011;
    assign parity_check_matrix[578] = 12'b010110000101;
    assign parity_check_matrix[579] = 12'b010110000110;
    assign parity_check_matrix[580] = 12'b010110001001;
    assign parity_check_matrix[581] = 12'b010110001010;
    assign parity_check_matrix[582] = 12'b010110001100;
    assign parity_check_matrix[583] = 12'b010110010001;
    assign parity_check_matrix[584] = 12'b010110010010;
    assign parity_check_matrix[585] = 12'b010110010100;
    assign parity_check_matrix[586] = 12'b010110011000;
    assign parity_check_matrix[587] = 12'b010110100001;
    assign parity_check_matrix[588] = 12'b010110100010;
    assign parity_check_matrix[589] = 12'b010110100100;
    assign parity_check_matrix[590] = 12'b010110101000;
    assign parity_check_matrix[591] = 12'b010110110000;
    assign parity_check_matrix[592] = 12'b010111000001;
    assign parity_check_matrix[593] = 12'b010111000010;
    assign parity_check_matrix[594] = 12'b010111000100;
    assign parity_check_matrix[595] = 12'b010111001000;
    assign parity_check_matrix[596] = 12'b010111010000;
    assign parity_check_matrix[597] = 12'b010111100000;
    assign parity_check_matrix[598] = 12'b011000000111;
    assign parity_check_matrix[599] = 12'b011000001011;
    assign parity_check_matrix[600] = 12'b011000001101;
    assign parity_check_matrix[601] = 12'b011000001110;
    assign parity_check_matrix[602] = 12'b011000010011;
    assign parity_check_matrix[603] = 12'b011000010101;
    assign parity_check_matrix[604] = 12'b011000010110;
    assign parity_check_matrix[605] = 12'b011000011001;
    assign parity_check_matrix[606] = 12'b011000011010;
    assign parity_check_matrix[607] = 12'b011000011100;
    assign parity_check_matrix[608] = 12'b011000100011;
    assign parity_check_matrix[609] = 12'b011000100101;
    assign parity_check_matrix[610] = 12'b011000100110;
    assign parity_check_matrix[611] = 12'b011000101001;
    assign parity_check_matrix[612] = 12'b011000101010;
    assign parity_check_matrix[613] = 12'b011000101100;
    assign parity_check_matrix[614] = 12'b011000110001;
    assign parity_check_matrix[615] = 12'b011000110010;
    assign parity_check_matrix[616] = 12'b011000110100;
    assign parity_check_matrix[617] = 12'b011000111000;
    assign parity_check_matrix[618] = 12'b011001000011;
    assign parity_check_matrix[619] = 12'b011001000101;
    assign parity_check_matrix[620] = 12'b011001000110;
    assign parity_check_matrix[621] = 12'b011001001001;
    assign parity_check_matrix[622] = 12'b011001001010;
    assign parity_check_matrix[623] = 12'b011001001100;
    assign parity_check_matrix[624] = 12'b011001010001;
    assign parity_check_matrix[625] = 12'b011001010010;
    assign parity_check_matrix[626] = 12'b011001010100;
    assign parity_check_matrix[627] = 12'b011001011000;
    assign parity_check_matrix[628] = 12'b011001100001;
    assign parity_check_matrix[629] = 12'b011001100010;
    assign parity_check_matrix[630] = 12'b011001100100;
    assign parity_check_matrix[631] = 12'b011001101000;
    assign parity_check_matrix[632] = 12'b011001110000;
    assign parity_check_matrix[633] = 12'b011010000011;
    assign parity_check_matrix[634] = 12'b011010000101;
    assign parity_check_matrix[635] = 12'b011010000110;
    assign parity_check_matrix[636] = 12'b011010001001;
    assign parity_check_matrix[637] = 12'b011010001010;
    assign parity_check_matrix[638] = 12'b011010001100;
    assign parity_check_matrix[639] = 12'b011010010001;
    assign parity_check_matrix[640] = 12'b011010010010;
    assign parity_check_matrix[641] = 12'b011010010100;
    assign parity_check_matrix[642] = 12'b011010011000;
    assign parity_check_matrix[643] = 12'b011010100001;
    assign parity_check_matrix[644] = 12'b011010100010;
    assign parity_check_matrix[645] = 12'b011010100100;
    assign parity_check_matrix[646] = 12'b011010101000;
    assign parity_check_matrix[647] = 12'b011010110000;
    assign parity_check_matrix[648] = 12'b011011000001;
    assign parity_check_matrix[649] = 12'b011011000010;
    assign parity_check_matrix[650] = 12'b011011000100;
    assign parity_check_matrix[651] = 12'b011011001000;
    assign parity_check_matrix[652] = 12'b011011010000;
    assign parity_check_matrix[653] = 12'b011011100000;
    assign parity_check_matrix[654] = 12'b011100000011;
    assign parity_check_matrix[655] = 12'b011100000101;
    assign parity_check_matrix[656] = 12'b011100000110;
    assign parity_check_matrix[657] = 12'b011100001001;
    assign parity_check_matrix[658] = 12'b011100001010;
    assign parity_check_matrix[659] = 12'b011100001100;
    assign parity_check_matrix[660] = 12'b011100010001;
    assign parity_check_matrix[661] = 12'b011100010010;
    assign parity_check_matrix[662] = 12'b011100010100;
    assign parity_check_matrix[663] = 12'b011100011000;
    assign parity_check_matrix[664] = 12'b011100100001;
    assign parity_check_matrix[665] = 12'b011100100010;
    assign parity_check_matrix[666] = 12'b011100100100;
    assign parity_check_matrix[667] = 12'b011100101000;
    assign parity_check_matrix[668] = 12'b011100110000;
    assign parity_check_matrix[669] = 12'b011101000001;
    assign parity_check_matrix[670] = 12'b011101000010;
    assign parity_check_matrix[671] = 12'b011101000100;
    assign parity_check_matrix[672] = 12'b011101001000;
    assign parity_check_matrix[673] = 12'b011101010000;
    assign parity_check_matrix[674] = 12'b011101100000;
    assign parity_check_matrix[675] = 12'b011110000001;
    assign parity_check_matrix[676] = 12'b011110000010;
    assign parity_check_matrix[677] = 12'b011110000100;
    assign parity_check_matrix[678] = 12'b011110001000;
    assign parity_check_matrix[679] = 12'b011110010000;
    assign parity_check_matrix[680] = 12'b011110100000;
    assign parity_check_matrix[681] = 12'b011111000000;
    assign parity_check_matrix[682] = 12'b100000001111;
    assign parity_check_matrix[683] = 12'b100000010111;
    assign parity_check_matrix[684] = 12'b100000011011;
    assign parity_check_matrix[685] = 12'b100000011101;
    assign parity_check_matrix[686] = 12'b100000011110;
    assign parity_check_matrix[687] = 12'b100000100111;
    assign parity_check_matrix[688] = 12'b100000101011;
    assign parity_check_matrix[689] = 12'b100000101101;
    assign parity_check_matrix[690] = 12'b100000101110;
    assign parity_check_matrix[691] = 12'b100000110011;
    assign parity_check_matrix[692] = 12'b100000110101;
    assign parity_check_matrix[693] = 12'b100000110110;
    assign parity_check_matrix[694] = 12'b100000111001;
    assign parity_check_matrix[695] = 12'b100000111010;
    assign parity_check_matrix[696] = 12'b100000111100;
    assign parity_check_matrix[697] = 12'b100001000111;
    assign parity_check_matrix[698] = 12'b100001001011;
    assign parity_check_matrix[699] = 12'b100001001101;
    assign parity_check_matrix[700] = 12'b100001001110;
    assign parity_check_matrix[701] = 12'b100001010011;
    assign parity_check_matrix[702] = 12'b100001010101;
    assign parity_check_matrix[703] = 12'b100001010110;
    assign parity_check_matrix[704] = 12'b100001011001;
    assign parity_check_matrix[705] = 12'b100001011010;
    assign parity_check_matrix[706] = 12'b100001011100;
    assign parity_check_matrix[707] = 12'b100001100011;
    assign parity_check_matrix[708] = 12'b100001100101;
    assign parity_check_matrix[709] = 12'b100001100110;
    assign parity_check_matrix[710] = 12'b100001101001;
    assign parity_check_matrix[711] = 12'b100001101010;
    assign parity_check_matrix[712] = 12'b100001101100;
    assign parity_check_matrix[713] = 12'b100001110001;
    assign parity_check_matrix[714] = 12'b100001110010;
    assign parity_check_matrix[715] = 12'b100001110100;
    assign parity_check_matrix[716] = 12'b100001111000;
    assign parity_check_matrix[717] = 12'b100010000111;
    assign parity_check_matrix[718] = 12'b100010001011;
    assign parity_check_matrix[719] = 12'b100010001101;
    assign parity_check_matrix[720] = 12'b100010001110;
    assign parity_check_matrix[721] = 12'b100010010011;
    assign parity_check_matrix[722] = 12'b100010010101;
    assign parity_check_matrix[723] = 12'b100010010110;
    assign parity_check_matrix[724] = 12'b100010011001;
    assign parity_check_matrix[725] = 12'b100010011010;
    assign parity_check_matrix[726] = 12'b100010011100;
    assign parity_check_matrix[727] = 12'b100010100011;
    assign parity_check_matrix[728] = 12'b100010100101;
    assign parity_check_matrix[729] = 12'b100010100110;
    assign parity_check_matrix[730] = 12'b100010101001;
    assign parity_check_matrix[731] = 12'b100010101010;
    assign parity_check_matrix[732] = 12'b100010101100;
    assign parity_check_matrix[733] = 12'b100010110001;
    assign parity_check_matrix[734] = 12'b100010110010;
    assign parity_check_matrix[735] = 12'b100010110100;
    assign parity_check_matrix[736] = 12'b100010111000;
    assign parity_check_matrix[737] = 12'b100011000011;
    assign parity_check_matrix[738] = 12'b100011000101;
    assign parity_check_matrix[739] = 12'b100011000110;
    assign parity_check_matrix[740] = 12'b100011001001;
    assign parity_check_matrix[741] = 12'b100011001010;
    assign parity_check_matrix[742] = 12'b100011001100;
    assign parity_check_matrix[743] = 12'b100011010001;
    assign parity_check_matrix[744] = 12'b100011010010;
    assign parity_check_matrix[745] = 12'b100011010100;
    assign parity_check_matrix[746] = 12'b100011011000;
    assign parity_check_matrix[747] = 12'b100011100001;
    assign parity_check_matrix[748] = 12'b100011100010;
    assign parity_check_matrix[749] = 12'b100011100100;
    assign parity_check_matrix[750] = 12'b100011101000;
    assign parity_check_matrix[751] = 12'b100011110000;
    assign parity_check_matrix[752] = 12'b100100000111;
    assign parity_check_matrix[753] = 12'b100100001011;
    assign parity_check_matrix[754] = 12'b100100001101;
    assign parity_check_matrix[755] = 12'b100100001110;
    assign parity_check_matrix[756] = 12'b100100010011;
    assign parity_check_matrix[757] = 12'b100100010101;
    assign parity_check_matrix[758] = 12'b100100010110;
    assign parity_check_matrix[759] = 12'b100100011001;
    assign parity_check_matrix[760] = 12'b100100011010;
    assign parity_check_matrix[761] = 12'b100100011100;
    assign parity_check_matrix[762] = 12'b100100100011;
    assign parity_check_matrix[763] = 12'b100100100101;
    assign parity_check_matrix[764] = 12'b100100100110;
    assign parity_check_matrix[765] = 12'b100100101001;
    assign parity_check_matrix[766] = 12'b100100101010;
    assign parity_check_matrix[767] = 12'b100100101100;
    assign parity_check_matrix[768] = 12'b100100110001;
    assign parity_check_matrix[769] = 12'b100100110010;
    assign parity_check_matrix[770] = 12'b100100110100;
    assign parity_check_matrix[771] = 12'b100100111000;
    assign parity_check_matrix[772] = 12'b100101000011;
    assign parity_check_matrix[773] = 12'b100101000101;
    assign parity_check_matrix[774] = 12'b100101000110;
    assign parity_check_matrix[775] = 12'b100101001001;
    assign parity_check_matrix[776] = 12'b100101001010;
    assign parity_check_matrix[777] = 12'b100101001100;
    assign parity_check_matrix[778] = 12'b100101010001;
    assign parity_check_matrix[779] = 12'b100101010010;
    assign parity_check_matrix[780] = 12'b100101010100;
    assign parity_check_matrix[781] = 12'b100101011000;
    assign parity_check_matrix[782] = 12'b100101100001;
    assign parity_check_matrix[783] = 12'b100101100010;
    assign parity_check_matrix[784] = 12'b100101100100;
    assign parity_check_matrix[785] = 12'b100101101000;
    assign parity_check_matrix[786] = 12'b100101110000;
    assign parity_check_matrix[787] = 12'b100110000011;
    assign parity_check_matrix[788] = 12'b100110000101;
    assign parity_check_matrix[789] = 12'b100110000110;
    assign parity_check_matrix[790] = 12'b100110001001;
    assign parity_check_matrix[791] = 12'b100110001010;
    assign parity_check_matrix[792] = 12'b100110001100;
    assign parity_check_matrix[793] = 12'b100110010001;
    assign parity_check_matrix[794] = 12'b100110010010;
    assign parity_check_matrix[795] = 12'b100110010100;
    assign parity_check_matrix[796] = 12'b100110011000;
    assign parity_check_matrix[797] = 12'b100110100001;
    assign parity_check_matrix[798] = 12'b100110100010;
    assign parity_check_matrix[799] = 12'b100110100100;
    assign parity_check_matrix[800] = 12'b100110101000;
    assign parity_check_matrix[801] = 12'b100110110000;
    assign parity_check_matrix[802] = 12'b100111000001;
    assign parity_check_matrix[803] = 12'b100111000010;
    assign parity_check_matrix[804] = 12'b100111000100;
    assign parity_check_matrix[805] = 12'b100111001000;
    assign parity_check_matrix[806] = 12'b100111010000;
    assign parity_check_matrix[807] = 12'b100111100000;
    assign parity_check_matrix[808] = 12'b101000000111;
    assign parity_check_matrix[809] = 12'b101000001011;
    assign parity_check_matrix[810] = 12'b101000001101;
    assign parity_check_matrix[811] = 12'b101000001110;
    assign parity_check_matrix[812] = 12'b101000010011;
    assign parity_check_matrix[813] = 12'b101000010101;
    assign parity_check_matrix[814] = 12'b101000010110;
    assign parity_check_matrix[815] = 12'b101000011001;
    assign parity_check_matrix[816] = 12'b101000011010;
    assign parity_check_matrix[817] = 12'b101000011100;
    assign parity_check_matrix[818] = 12'b101000100011;
    assign parity_check_matrix[819] = 12'b101000100101;
    assign parity_check_matrix[820] = 12'b101000100110;
    assign parity_check_matrix[821] = 12'b101000101001;
    assign parity_check_matrix[822] = 12'b101000101010;
    assign parity_check_matrix[823] = 12'b101000101100;
    assign parity_check_matrix[824] = 12'b101000110001;
    assign parity_check_matrix[825] = 12'b101000110010;
    assign parity_check_matrix[826] = 12'b101000110100;
    assign parity_check_matrix[827] = 12'b101000111000;
    assign parity_check_matrix[828] = 12'b101001000011;
    assign parity_check_matrix[829] = 12'b101001000101;
    assign parity_check_matrix[830] = 12'b101001000110;
    assign parity_check_matrix[831] = 12'b101001001001;
    assign parity_check_matrix[832] = 12'b101001001010;
    assign parity_check_matrix[833] = 12'b101001001100;
    assign parity_check_matrix[834] = 12'b101001010001;
    assign parity_check_matrix[835] = 12'b101001010010;
    assign parity_check_matrix[836] = 12'b101001010100;
    assign parity_check_matrix[837] = 12'b101001011000;
    assign parity_check_matrix[838] = 12'b101001100001;
    assign parity_check_matrix[839] = 12'b101001100010;
    assign parity_check_matrix[840] = 12'b101001100100;
    assign parity_check_matrix[841] = 12'b101001101000;
    assign parity_check_matrix[842] = 12'b101001110000;
    assign parity_check_matrix[843] = 12'b101010000011;
    assign parity_check_matrix[844] = 12'b101010000101;
    assign parity_check_matrix[845] = 12'b101010000110;
    assign parity_check_matrix[846] = 12'b101010001001;
    assign parity_check_matrix[847] = 12'b101010001010;
    assign parity_check_matrix[848] = 12'b101010001100;
    assign parity_check_matrix[849] = 12'b101010010001;
    assign parity_check_matrix[850] = 12'b101010010010;
    assign parity_check_matrix[851] = 12'b101010010100;
    assign parity_check_matrix[852] = 12'b101010011000;
    assign parity_check_matrix[853] = 12'b101010100001;
    assign parity_check_matrix[854] = 12'b101010100010;
    assign parity_check_matrix[855] = 12'b101010100100;
    assign parity_check_matrix[856] = 12'b101010101000;
    assign parity_check_matrix[857] = 12'b101010110000;
    assign parity_check_matrix[858] = 12'b101011000001;
    assign parity_check_matrix[859] = 12'b101011000010;
    assign parity_check_matrix[860] = 12'b101011000100;
    assign parity_check_matrix[861] = 12'b101011001000;
    assign parity_check_matrix[862] = 12'b101011010000;
    assign parity_check_matrix[863] = 12'b101011100000;
    assign parity_check_matrix[864] = 12'b101100000011;
    assign parity_check_matrix[865] = 12'b101100000101;
    assign parity_check_matrix[866] = 12'b101100000110;
    assign parity_check_matrix[867] = 12'b101100001001;
    assign parity_check_matrix[868] = 12'b101100001010;
    assign parity_check_matrix[869] = 12'b101100001100;
    assign parity_check_matrix[870] = 12'b101100010001;
    assign parity_check_matrix[871] = 12'b101100010010;
    assign parity_check_matrix[872] = 12'b101100010100;
    assign parity_check_matrix[873] = 12'b101100011000;
    assign parity_check_matrix[874] = 12'b101100100001;
    assign parity_check_matrix[875] = 12'b101100100010;
    assign parity_check_matrix[876] = 12'b101100100100;
    assign parity_check_matrix[877] = 12'b101100101000;
    assign parity_check_matrix[878] = 12'b101100110000;
    assign parity_check_matrix[879] = 12'b101101000001;
    assign parity_check_matrix[880] = 12'b101101000010;
    assign parity_check_matrix[881] = 12'b101101000100;
    assign parity_check_matrix[882] = 12'b101101001000;
    assign parity_check_matrix[883] = 12'b101101010000;
    assign parity_check_matrix[884] = 12'b101101100000;
    assign parity_check_matrix[885] = 12'b101110000001;
    assign parity_check_matrix[886] = 12'b101110000010;
    assign parity_check_matrix[887] = 12'b101110000100;
    assign parity_check_matrix[888] = 12'b101110001000;
    assign parity_check_matrix[889] = 12'b101110010000;
    assign parity_check_matrix[890] = 12'b101110100000;
    assign parity_check_matrix[891] = 12'b101111000000;
    assign parity_check_matrix[892] = 12'b110000000111;
    assign parity_check_matrix[893] = 12'b110000001011;
    assign parity_check_matrix[894] = 12'b110000001101;
    assign parity_check_matrix[895] = 12'b110000001110;
    assign parity_check_matrix[896] = 12'b110000010011;
    assign parity_check_matrix[897] = 12'b110000010101;
    assign parity_check_matrix[898] = 12'b110000010110;
    assign parity_check_matrix[899] = 12'b110000011001;
    assign parity_check_matrix[900] = 12'b110000011010;
    assign parity_check_matrix[901] = 12'b110000011100;
    assign parity_check_matrix[902] = 12'b110000100011;
    assign parity_check_matrix[903] = 12'b110000100101;
    assign parity_check_matrix[904] = 12'b110000100110;
    assign parity_check_matrix[905] = 12'b110000101001;
    assign parity_check_matrix[906] = 12'b110000101010;
    assign parity_check_matrix[907] = 12'b110000101100;
    assign parity_check_matrix[908] = 12'b110000110001;
    assign parity_check_matrix[909] = 12'b110000110010;
    assign parity_check_matrix[910] = 12'b110000110100;
    assign parity_check_matrix[911] = 12'b110000111000;
    assign parity_check_matrix[912] = 12'b110001000011;
    assign parity_check_matrix[913] = 12'b110001000101;
    assign parity_check_matrix[914] = 12'b110001000110;
    assign parity_check_matrix[915] = 12'b110001001001;
    assign parity_check_matrix[916] = 12'b110001001010;
    assign parity_check_matrix[917] = 12'b110001001100;
    assign parity_check_matrix[918] = 12'b110001010001;
    assign parity_check_matrix[919] = 12'b110001010010;
    assign parity_check_matrix[920] = 12'b110001010100;
    assign parity_check_matrix[921] = 12'b110001011000;
    assign parity_check_matrix[922] = 12'b110001100001;
    assign parity_check_matrix[923] = 12'b110001100010;
    assign parity_check_matrix[924] = 12'b110001100100;
    assign parity_check_matrix[925] = 12'b110001101000;
    assign parity_check_matrix[926] = 12'b110001110000;
    assign parity_check_matrix[927] = 12'b110010000011;
    assign parity_check_matrix[928] = 12'b110010000101;
    assign parity_check_matrix[929] = 12'b110010000110;
    assign parity_check_matrix[930] = 12'b110010001001;
    assign parity_check_matrix[931] = 12'b110010001010;
    assign parity_check_matrix[932] = 12'b110010001100;
    assign parity_check_matrix[933] = 12'b110010010001;
    assign parity_check_matrix[934] = 12'b110010010010;
    assign parity_check_matrix[935] = 12'b110010010100;
    assign parity_check_matrix[936] = 12'b110010011000;
    assign parity_check_matrix[937] = 12'b110010100001;
    assign parity_check_matrix[938] = 12'b110010100010;
    assign parity_check_matrix[939] = 12'b110010100100;
    assign parity_check_matrix[940] = 12'b110010101000;
    assign parity_check_matrix[941] = 12'b110010110000;
    assign parity_check_matrix[942] = 12'b110011000001;
    assign parity_check_matrix[943] = 12'b110011000010;
    assign parity_check_matrix[944] = 12'b110011000100;
    assign parity_check_matrix[945] = 12'b110011001000;
    assign parity_check_matrix[946] = 12'b110011010000;
    assign parity_check_matrix[947] = 12'b110011100000;
    assign parity_check_matrix[948] = 12'b110100000011;
    assign parity_check_matrix[949] = 12'b110100000101;
    assign parity_check_matrix[950] = 12'b110100000110;
    assign parity_check_matrix[951] = 12'b110100001001;
    assign parity_check_matrix[952] = 12'b110100001010;
    assign parity_check_matrix[953] = 12'b110100001100;
    assign parity_check_matrix[954] = 12'b110100010001;
    assign parity_check_matrix[955] = 12'b110100010010;
    assign parity_check_matrix[956] = 12'b110100010100;
    assign parity_check_matrix[957] = 12'b110100011000;
    assign parity_check_matrix[958] = 12'b110100100001;
    assign parity_check_matrix[959] = 12'b110100100010;
    assign parity_check_matrix[960] = 12'b110100100100;
    assign parity_check_matrix[961] = 12'b110100101000;
    assign parity_check_matrix[962] = 12'b110100110000;
    assign parity_check_matrix[963] = 12'b110101000001;
    assign parity_check_matrix[964] = 12'b110101000010;
    assign parity_check_matrix[965] = 12'b110101000100;
    assign parity_check_matrix[966] = 12'b110101001000;
    assign parity_check_matrix[967] = 12'b110101010000;
    assign parity_check_matrix[968] = 12'b110101100000;
    assign parity_check_matrix[969] = 12'b110110000001;
    assign parity_check_matrix[970] = 12'b110110000010;
    assign parity_check_matrix[971] = 12'b110110000100;
    assign parity_check_matrix[972] = 12'b110110001000;
    assign parity_check_matrix[973] = 12'b110110010000;
    assign parity_check_matrix[974] = 12'b110110100000;
    assign parity_check_matrix[975] = 12'b110111000000;
    assign parity_check_matrix[976] = 12'b111000000011;
    assign parity_check_matrix[977] = 12'b111000000101;
    assign parity_check_matrix[978] = 12'b111000000110;
    assign parity_check_matrix[979] = 12'b111000001001;
    assign parity_check_matrix[980] = 12'b111000001010;
    assign parity_check_matrix[981] = 12'b111000001100;
    assign parity_check_matrix[982] = 12'b111000010001;
    assign parity_check_matrix[983] = 12'b111000010010;
    assign parity_check_matrix[984] = 12'b111000010100;
    assign parity_check_matrix[985] = 12'b111000011000;
    assign parity_check_matrix[986] = 12'b111000100001;
    assign parity_check_matrix[987] = 12'b111000100010;
    assign parity_check_matrix[988] = 12'b111000100100;
    assign parity_check_matrix[989] = 12'b111000101000;
    assign parity_check_matrix[990] = 12'b111000110000;
    assign parity_check_matrix[991] = 12'b111001000001;
    assign parity_check_matrix[992] = 12'b111001000010;
    assign parity_check_matrix[993] = 12'b111001000100;
    assign parity_check_matrix[994] = 12'b111001001000;
    assign parity_check_matrix[995] = 12'b111001010000;
    assign parity_check_matrix[996] = 12'b111001100000;
    assign parity_check_matrix[997] = 12'b111010000001;
    assign parity_check_matrix[998] = 12'b111010000010;
    assign parity_check_matrix[999] = 12'b111010000100;
    assign parity_check_matrix[1000] = 12'b111010001000;
    assign parity_check_matrix[1001] = 12'b111010010000;
    assign parity_check_matrix[1002] = 12'b111010100000;
    assign parity_check_matrix[1003] = 12'b111011000000;
    assign parity_check_matrix[1004] = 12'b111100000001;
    assign parity_check_matrix[1005] = 12'b111100000010;
    assign parity_check_matrix[1006] = 12'b111100000100;
    assign parity_check_matrix[1007] = 12'b111100001000;
    assign parity_check_matrix[1008] = 12'b111100010000;
    assign parity_check_matrix[1009] = 12'b111100100000;
    assign parity_check_matrix[1010] = 12'b111101000000;
    assign parity_check_matrix[1011] = 12'b111110000000;
    assign parity_check_matrix[1012] = 12'b000001111111;
    assign parity_check_matrix[1013] = 12'b000010111111;
    assign parity_check_matrix[1014] = 12'b000011011111;
    assign parity_check_matrix[1015] = 12'b000011101111;
    assign parity_check_matrix[1016] = 12'b000011110111;
    assign parity_check_matrix[1017] = 12'b000011111011;
    assign parity_check_matrix[1018] = 12'b000011111101;
    assign parity_check_matrix[1019] = 12'b000011111110;
    assign parity_check_matrix[1020] = 12'b000100111111;
    assign parity_check_matrix[1021] = 12'b000101011111;
    assign parity_check_matrix[1022] = 12'b000101101111;
    assign parity_check_matrix[1023] = 12'b000101110111;
    assign parity_check_matrix[1024] = 12'b100000000000;
    assign parity_check_matrix[1025] = 12'b010000000000;
    assign parity_check_matrix[1026] = 12'b001000000000;
    assign parity_check_matrix[1027] = 12'b000100000000;
    assign parity_check_matrix[1028] = 12'b000010000000;
    assign parity_check_matrix[1029] = 12'b000001000000;
    assign parity_check_matrix[1030] = 12'b000000100000;
    assign parity_check_matrix[1031] = 12'b000000010000;
    assign parity_check_matrix[1032] = 12'b000000001000;
    assign parity_check_matrix[1033] = 12'b000000000100;
    assign parity_check_matrix[1034] = 12'b000000000010;
    assign parity_check_matrix[1035] = 12'b000000000001;
  end else begin : gen_default_parity
    `BR_ASSERT_STATIC(invalid_parity_width_a, 1'b0)
  end

  // ri lint_check_on EXPR_ID_LIMIT

  //------
  // Optionally register the syndrome before decoding.
  //------
  logic internal_valid;
  logic [CodewordWidth-1:0] internal_codeword;
  logic [ParityWidth-1:0] internal_error_syndrome;

  br_delay_valid #(
      .Width(CodewordWidth + ParityWidth),
      .NumStages(RegisterSyndrome)
  ) br_delay_valid_syndrome (
      .clk,
      .rst,
      .in_valid(codeword_valid),
      .in({codeword, syndrome}),
      .out_valid(internal_valid),
      .out({internal_codeword, internal_error_syndrome}),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------
  // Decode syndrome.
  //------
  // * Case 0: Syndrome is zero, no errors detected.
  // * Case 1: Syndrome is for a nonzero even number of bits in error, which happens when
  //   the syndrome is nonzero and even in a Hsiao SECDED code.
  //   Maximum likelihood decoding produces multiple equiprobable candidate codewords, so
  //   treat as detected-but-uncorrectable.
  //   NOTE: We are returning *some* message but it is likely to have been corrupted!
  // * Case 2: Syndrome is for an odd number of bits in error, which happens when the syndrome
  //   is odd in a Hsiao SECDED code.
  //   * Case 2a: Rarely this can be a three-bit error that is actually detected-but-uncorrectable.
  //   * Case 2b: Usually this is a single-bit error, which is always closest to exactly one codeword.
  //     So with maximum likelihood decoding we can correct it.
  logic internal_error_syndrome_parity;
  logic internal_error_syndrome_is_zero;
  logic internal_error_syndrome_is_even;
  logic internal_error_syndrome_is_odd;

  assign internal_error_syndrome_parity  = ^internal_error_syndrome;
  assign internal_error_syndrome_is_zero = internal_error_syndrome == '0;
  assign internal_error_syndrome_is_even = !internal_error_syndrome_parity;
  assign internal_error_syndrome_is_odd  = internal_error_syndrome_parity;

  // Case 0 (no errors detected) -- implicitly true if case 1, 2a, and 2b are all false.

  // Case 1 (detected-but-uncorrectable with nonzero and even syndrome)
  logic internal_due_even;
  assign internal_due_even = !internal_error_syndrome_is_zero && internal_error_syndrome_is_even;

  // Case 2 - need more information to decide if it's case 2a or 2b.
  logic [CodewordWidth-1:0] internal_h_column_match;
  for (genvar i = 0; i < CodewordWidth; i++) begin : gen_col_match
    assign internal_h_column_match[i] = (internal_error_syndrome == parity_check_matrix[i]);
  end

  // Case 2a (detected-but-uncorrectable with odd syndrome)
  // This happens when the syndrome is odd but it doesn't match any of the columns in H.
  // Since the code is guaranteed to correct any single-bit error, this means it must be
  // an odd number (at least 3) of bits in error.
  logic internal_due_odd;
  assign internal_due_odd = internal_error_syndrome_is_odd && (internal_h_column_match == '0);

  // Merge case 1 and 2a (detected-but-uncorrectable)
  logic internal_error_due;
  assign internal_error_due = (internal_due_even || internal_due_odd);

  // Case 2b (correctable with single-bit error)
  logic internal_error_corrected;
  assign internal_error_corrected =
    internal_error_syndrome_is_odd && (internal_h_column_match != '0);

  //------
  // Correct the codeword (if necessary and possible), then extract the message and data.
  //------
  // If there was a DUE, then the corrected codeword is still corrupted and
  // the message and data are likely to also be corrupted.

  logic [CodewordWidth-1:0] internal_corrected_codeword;
  logic [ MessageWidth-1:0] internal_message;
  logic [DataWidth-1:0] internal_data;

  assign internal_corrected_codeword = internal_codeword ^ internal_h_column_match;
  assign internal_message = internal_corrected_codeword[MessageWidth-1:0];

  `BR_UNUSED_NAMED(corrected_codeword_parity,
    internal_corrected_codeword[CodewordWidth-1:MessageWidth])

  if (MessageWidth > DataWidth) begin : gen_pad
    assign internal_data = internal_message[DataWidth-1:0];
    `BR_UNUSED_NAMED(messsage_pad, internal_message[MessageWidth-1:DataWidth])
  end else begin : gen_no_pad
    assign internal_data = internal_message;
  end

  `BR_ASSERT_IMPL(internal_h_column_match_onehot0_a,
                  internal_valid |-> $onehot0(internal_h_column_match))
  `BR_ASSERT_IMPL(due_no_h_column_match_a,
                  internal_valid && internal_error_due |->
                  (internal_h_column_match == '0))
  `BR_ASSERT_IMPL(no_error_correction_a,
                  internal_valid && !internal_error_corrected |->
                  (internal_corrected_codeword == internal_codeword))
  `BR_ASSERT_IMPL(error_correction_a,
                  internal_valid && internal_error_corrected |->
                  (internal_corrected_codeword != internal_codeword))

  //------
  // Optionally register the output signals.
  //------
  br_delay_valid #(
      .Width({(DataWidth + 32'd2) + ParityWidth}),
      .NumStages(RegisterOutputs == 1 ? 1 : 0)
  ) br_delay_valid_outputs (
      .clk,
      .rst,
      .in_valid(internal_valid),
      .in({internal_data,
          internal_error_corrected,
          internal_error_due,
          internal_error_syndrome}),
      .out_valid(data_valid),
      .out({data,
            data_error_corrected,
            data_error_detected_but_uncorrectable,
            data_error_syndrome}),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(latency_a, codeword_valid |-> ##Latency data_valid)
  `BR_ASSERT_IMPL(ce_due_mutually_exclusive_a,
                  data_valid |-> $onehot0({data_error_corrected, data_error_detected_but_uncorrectable}))
  `BR_COVER_IMPL(ce_c, data_valid && data_error_corrected)
  `BR_COVER_IMPL(due_c, data_valid && data_error_detected_but_uncorrectable)

  // verilog_format: on
  // verilog_lint: waive-stop line-length

endmodule : br_ecc_secded_decoder
