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
// This module has parameterizable latency. By default, it is purely combinational,
// but it can have up to 3 cycles of delay (RegisterInputs, RegisterSyndrome, and
// RegisterOutputs). The initiation interval is always 1 cycle.
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
`include "br_assign.svh"
`include "br_unused.svh"

// TODO(mgottscho): Pipeline the syndrome decoding and then correction with a parameter.
module br_ecc_secded_decoder #(
    parameter int DataWidth = 1,  // Must be at least 1
    parameter int ParityWidth = 4,  // Must be at least 4 and at most 12
    // If 1, then insert a pipeline register at the input.
    parameter bit RegisterInputs = 0,
    // If 1, then insert a pipeline register between syndrome computation and
    // syndrome decoding (error correction).
    parameter bit RegisterSyndrome = 0,
    // If 1, then insert a pipeline register at the output.
    parameter bit RegisterOutputs = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int InputWidth = DataWidth + ParityWidth,
    localparam int MessageWidth = 2 ** $clog2(DataWidth),
    localparam int CodewordWidth = MessageWidth + ParityWidth,
    // ri lint_check_waive PARAM_NOT_USED
    localparam int Latency = RegisterInputs + RegisterSyndrome + RegisterOutputs
) (
    // Positive edge-triggered clock.
    input  logic                     clk,
    // Synchronous active-high reset.
    input  logic                     rst,

    // Decoder input (received codeword, possibly with errors)
    input  logic                     rcv_valid,
    input  logic [    DataWidth-1:0] rcv_data,
    input  logic [  ParityWidth-1:0] rcv_parity,

    // Decoder output
    output logic                     dec_valid,
    output logic [   InputWidth-1:0] dec_codeword,
    output logic                     dec_error_ce,  // corrected error
    output logic                     dec_error_due,  // detected-but-uncorrectable error
    output logic [  ParityWidth-1:0] dec_error_syndrome,
    output logic [    DataWidth-1:0] dec_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(message_width_gte_1_a, DataWidth >= 1)
  `BR_ASSERT_STATIC(parity_width_gte_4_a, ParityWidth >= 4)
  `BR_ASSERT_STATIC(parity_width_lte_12_a, ParityWidth <= 12)

  //------------------------------------------
  // Implementation
  //------------------------------------------

  //------
  // Optionally register the input signals.
  //------
  logic rcv_valid_d;
  logic [InputWidth-1:0] rcv_codeword_d;

  br_delay_valid #(
      .Width(InputWidth),
      .NumStages(RegisterInputs == 1 ? 1 : 0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_inputs (
      .clk,
      .rst,
      .in_valid(rcv_valid),
      .in({rcv_parity, rcv_data}),
      .out_valid(rcv_valid_d),
      .out(rcv_codeword_d),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------
  // Compute syndrome and set up constant parity check matrix.
  //------
  logic [CodewordWidth-1:0][ParityWidth-1:0] parity_check_matrix;  // H
  logic [ParityWidth-1:0] syndrome;
  logic [CodewordWidth-1:0] cw;  // shorten name for internal readability
  assign `BR_INSERT_TO_MSB(cw, rcv_codeword_d[InputWidth-1 -: ParityWidth])
  if (CodewordWidth > InputWidth) begin : gen_cw_pad_bits
    assign cw[MessageWidth -1 : DataWidth] = '0;
  end
  assign `BR_INSERT_TO_LSB(cw, rcv_codeword_d[DataWidth-1:0])

  // ri lint_check_off EXPR_ID_LIMIT

  if ((CodewordWidth == 4) && (MessageWidth == 4)) begin : gen_8_4
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 4)
    assign syndrome[0] = cw[1] ^ cw[2] ^ cw[3] ^ cw[4];
    assign syndrome[1] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5];
    assign syndrome[2] = cw[0] ^ cw[1] ^ cw[3] ^ cw[6];
    assign syndrome[3] = cw[0] ^ cw[1] ^ cw[2] ^ cw[7];
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
    assign syndrome[0] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8];
    assign syndrome[1] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[9];
    assign syndrome[2] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[10];
    assign syndrome[3] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[11];
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[12];
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
    assign syndrome[0] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16];
    assign syndrome[1] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[17];
    assign syndrome[2] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[18];
    assign syndrome[3] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[19];
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[20];
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[21];
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
    assign syndrome[0] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32];
    assign syndrome[1] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[33];
    assign syndrome[2] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34];
    assign syndrome[3] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[35];
    assign syndrome[4] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[36];
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[37];
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[38];
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
    assign syndrome[0] = cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[64];
    assign syndrome[1] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[62] ^ cw[63] ^ cw[65];
    assign syndrome[2] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[55] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[66];
    assign syndrome[3] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[56] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[63] ^ cw[67];
    assign syndrome[4] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[33] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[44] ^ cw[48] ^ cw[53] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[68];
    assign syndrome[5] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[32] ^ cw[36] ^ cw[37] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[52] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[69];
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[35] ^ cw[37] ^ cw[39] ^ cw[42] ^ cw[46] ^ cw[51] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[70];
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[38] ^ cw[41] ^ cw[45] ^ cw[50] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[62] ^ cw[63] ^ cw[71];
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
    assign syndrome[0] = cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[128];
    assign syndrome[1] = cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[129];
    assign syndrome[2] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[83] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[130];
    assign syndrome[3] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[55] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[76] ^ cw[82] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[131];
    assign syndrome[4] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[70] ^ cw[75] ^ cw[81] ^ cw[84] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[132];
    assign syndrome[5] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[33] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[44] ^ cw[48] ^ cw[53] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[65] ^ cw[69] ^ cw[74] ^ cw[80] ^ cw[84] ^ cw[85] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[127] ^ cw[133];
    assign syndrome[6] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[32] ^ cw[36] ^ cw[37] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[52] ^ cw[57] ^ cw[58] ^ cw[61] ^ cw[64] ^ cw[68] ^ cw[73] ^ cw[79] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[97] ^ cw[98] ^ cw[100] ^ cw[101] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[112] ^ cw[113] ^ cw[115] ^ cw[116] ^ cw[119] ^ cw[120] ^ cw[122] ^ cw[123] ^ cw[125] ^ cw[126] ^ cw[134];
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[35] ^ cw[37] ^ cw[39] ^ cw[42] ^ cw[46] ^ cw[51] ^ cw[56] ^ cw[58] ^ cw[60] ^ cw[63] ^ cw[67] ^ cw[72] ^ cw[78] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[98] ^ cw[99] ^ cw[101] ^ cw[103] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[113] ^ cw[114] ^ cw[116] ^ cw[118] ^ cw[120] ^ cw[121] ^ cw[123] ^ cw[124] ^ cw[126] ^ cw[135];
    assign syndrome[8] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[38] ^ cw[41] ^ cw[45] ^ cw[50] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[62] ^ cw[66] ^ cw[71] ^ cw[77] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[99] ^ cw[100] ^ cw[102] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[114] ^ cw[115] ^ cw[117] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[124] ^ cw[125] ^ cw[127] ^ cw[136];
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
    assign syndrome[0] = cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[256];
    assign syndrome[1] = cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[257];
    assign syndrome[2] = cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[119] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[258];
    assign syndrome[3] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[83] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[111] ^ cw[118] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[259];
    assign syndrome[4] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[55] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[76] ^ cw[82] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[104] ^ cw[110] ^ cw[117] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[260];
    assign syndrome[5] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[70] ^ cw[75] ^ cw[81] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[98] ^ cw[103] ^ cw[109] ^ cw[116] ^ cw[120] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[245] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[255] ^ cw[261];
    assign syndrome[6] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[33] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[44] ^ cw[48] ^ cw[53] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[65] ^ cw[69] ^ cw[74] ^ cw[80] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[93] ^ cw[97] ^ cw[102] ^ cw[108] ^ cw[115] ^ cw[120] ^ cw[121] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[175] ^ cw[176] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[210] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[230] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[240] ^ cw[244] ^ cw[246] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[262];
    assign syndrome[7] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[32] ^ cw[36] ^ cw[37] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[52] ^ cw[57] ^ cw[58] ^ cw[61] ^ cw[64] ^ cw[68] ^ cw[73] ^ cw[79] ^ cw[85] ^ cw[86] ^ cw[89] ^ cw[92] ^ cw[96] ^ cw[101] ^ cw[107] ^ cw[114] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[133] ^ cw[134] ^ cw[136] ^ cw[137] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[148] ^ cw[149] ^ cw[151] ^ cw[152] ^ cw[155] ^ cw[156] ^ cw[158] ^ cw[159] ^ cw[161] ^ cw[162] ^ cw[165] ^ cw[167] ^ cw[168] ^ cw[171] ^ cw[174] ^ cw[176] ^ cw[177] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[183] ^ cw[184] ^ cw[186] ^ cw[187] ^ cw[190] ^ cw[191] ^ cw[193] ^ cw[194] ^ cw[196] ^ cw[197] ^ cw[200] ^ cw[202] ^ cw[203] ^ cw[206] ^ cw[209] ^ cw[211] ^ cw[213] ^ cw[214] ^ cw[216] ^ cw[217] ^ cw[220] ^ cw[222] ^ cw[223] ^ cw[226] ^ cw[229] ^ cw[232] ^ cw[233] ^ cw[236] ^ cw[239] ^ cw[243] ^ cw[246] ^ cw[247] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[253] ^ cw[254] ^ cw[263];
    assign syndrome[8] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[35] ^ cw[37] ^ cw[39] ^ cw[42] ^ cw[46] ^ cw[51] ^ cw[56] ^ cw[58] ^ cw[60] ^ cw[63] ^ cw[67] ^ cw[72] ^ cw[78] ^ cw[84] ^ cw[86] ^ cw[88] ^ cw[91] ^ cw[95] ^ cw[100] ^ cw[106] ^ cw[113] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[134] ^ cw[135] ^ cw[137] ^ cw[139] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[149] ^ cw[150] ^ cw[152] ^ cw[154] ^ cw[156] ^ cw[157] ^ cw[159] ^ cw[160] ^ cw[162] ^ cw[164] ^ cw[166] ^ cw[168] ^ cw[170] ^ cw[173] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[184] ^ cw[185] ^ cw[187] ^ cw[189] ^ cw[191] ^ cw[192] ^ cw[194] ^ cw[195] ^ cw[197] ^ cw[199] ^ cw[201] ^ cw[203] ^ cw[205] ^ cw[208] ^ cw[211] ^ cw[212] ^ cw[214] ^ cw[215] ^ cw[217] ^ cw[219] ^ cw[221] ^ cw[223] ^ cw[225] ^ cw[228] ^ cw[231] ^ cw[233] ^ cw[235] ^ cw[238] ^ cw[242] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[254] ^ cw[255] ^ cw[264];
    assign syndrome[9] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[38] ^ cw[41] ^ cw[45] ^ cw[50] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[62] ^ cw[66] ^ cw[71] ^ cw[77] ^ cw[84] ^ cw[85] ^ cw[87] ^ cw[90] ^ cw[94] ^ cw[99] ^ cw[105] ^ cw[112] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[135] ^ cw[136] ^ cw[138] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[150] ^ cw[151] ^ cw[153] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[160] ^ cw[161] ^ cw[163] ^ cw[166] ^ cw[167] ^ cw[169] ^ cw[172] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[185] ^ cw[186] ^ cw[188] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[195] ^ cw[196] ^ cw[198] ^ cw[201] ^ cw[202] ^ cw[204] ^ cw[207] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[215] ^ cw[216] ^ cw[218] ^ cw[221] ^ cw[222] ^ cw[224] ^ cw[227] ^ cw[231] ^ cw[232] ^ cw[234] ^ cw[237] ^ cw[241] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[255] ^ cw[265];
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
    assign syndrome[0] = cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[420] ^ cw[421] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[511] ^ cw[512];
    assign syndrome[1] = cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[295] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[416] ^ cw[513];
    assign syndrome[2] = cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[164] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[416] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[511] ^ cw[514];
    assign syndrome[3] = cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[119] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[155] ^ cw[163] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[416] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[515];
    assign syndrome[4] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[83] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[111] ^ cw[118] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[147] ^ cw[154] ^ cw[162] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[416] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[511] ^ cw[516];
    assign syndrome[5] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[55] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[76] ^ cw[82] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[104] ^ cw[110] ^ cw[117] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[140] ^ cw[146] ^ cw[153] ^ cw[161] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[416] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[517];
    assign syndrome[6] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[70] ^ cw[75] ^ cw[81] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[98] ^ cw[103] ^ cw[109] ^ cw[116] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[134] ^ cw[139] ^ cw[145] ^ cw[152] ^ cw[160] ^ cw[165] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[290] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[295] ^ cw[300] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[310] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[330] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[360] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[395] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[410] ^ cw[415] ^ cw[418] ^ cw[419] ^ cw[420] ^ cw[421] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[486] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[518];
    assign syndrome[7] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[33] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[44] ^ cw[48] ^ cw[53] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[65] ^ cw[69] ^ cw[74] ^ cw[80] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[93] ^ cw[97] ^ cw[102] ^ cw[108] ^ cw[115] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[129] ^ cw[133] ^ cw[138] ^ cw[144] ^ cw[151] ^ cw[159] ^ cw[165] ^ cw[166] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[220] ^ cw[221] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[255] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[275] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[285] ^ cw[289] ^ cw[291] ^ cw[293] ^ cw[294] ^ cw[295] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[325] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[345] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[355] ^ cw[359] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[380] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[390] ^ cw[394] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[405] ^ cw[409] ^ cw[414] ^ cw[417] ^ cw[419] ^ cw[420] ^ cw[421] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[451] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[471] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[481] ^ cw[485] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[506] ^ cw[510] ^ cw[511] ^ cw[519];
    assign syndrome[8] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[32] ^ cw[36] ^ cw[37] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[52] ^ cw[57] ^ cw[58] ^ cw[61] ^ cw[64] ^ cw[68] ^ cw[73] ^ cw[79] ^ cw[85] ^ cw[86] ^ cw[89] ^ cw[92] ^ cw[96] ^ cw[101] ^ cw[107] ^ cw[114] ^ cw[121] ^ cw[122] ^ cw[125] ^ cw[128] ^ cw[132] ^ cw[137] ^ cw[143] ^ cw[150] ^ cw[158] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[178] ^ cw[179] ^ cw[181] ^ cw[182] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[193] ^ cw[194] ^ cw[196] ^ cw[197] ^ cw[200] ^ cw[201] ^ cw[203] ^ cw[204] ^ cw[206] ^ cw[207] ^ cw[210] ^ cw[212] ^ cw[213] ^ cw[216] ^ cw[219] ^ cw[221] ^ cw[222] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[228] ^ cw[229] ^ cw[231] ^ cw[232] ^ cw[235] ^ cw[236] ^ cw[238] ^ cw[239] ^ cw[241] ^ cw[242] ^ cw[245] ^ cw[247] ^ cw[248] ^ cw[251] ^ cw[254] ^ cw[256] ^ cw[258] ^ cw[259] ^ cw[261] ^ cw[262] ^ cw[265] ^ cw[267] ^ cw[268] ^ cw[271] ^ cw[274] ^ cw[277] ^ cw[278] ^ cw[281] ^ cw[284] ^ cw[288] ^ cw[291] ^ cw[292] ^ cw[294] ^ cw[295] ^ cw[296] ^ cw[298] ^ cw[299] ^ cw[301] ^ cw[302] ^ cw[305] ^ cw[306] ^ cw[308] ^ cw[309] ^ cw[311] ^ cw[312] ^ cw[315] ^ cw[317] ^ cw[318] ^ cw[321] ^ cw[324] ^ cw[326] ^ cw[328] ^ cw[329] ^ cw[331] ^ cw[332] ^ cw[335] ^ cw[337] ^ cw[338] ^ cw[341] ^ cw[344] ^ cw[347] ^ cw[348] ^ cw[351] ^ cw[354] ^ cw[358] ^ cw[361] ^ cw[363] ^ cw[364] ^ cw[366] ^ cw[367] ^ cw[370] ^ cw[372] ^ cw[373] ^ cw[376] ^ cw[379] ^ cw[382] ^ cw[383] ^ cw[386] ^ cw[389] ^ cw[393] ^ cw[397] ^ cw[398] ^ cw[401] ^ cw[404] ^ cw[408] ^ cw[413] ^ cw[417] ^ cw[418] ^ cw[420] ^ cw[421] ^ cw[422] ^ cw[424] ^ cw[425] ^ cw[427] ^ cw[428] ^ cw[431] ^ cw[432] ^ cw[434] ^ cw[435] ^ cw[437] ^ cw[438] ^ cw[441] ^ cw[443] ^ cw[444] ^ cw[447] ^ cw[450] ^ cw[452] ^ cw[454] ^ cw[455] ^ cw[457] ^ cw[458] ^ cw[461] ^ cw[463] ^ cw[464] ^ cw[467] ^ cw[470] ^ cw[473] ^ cw[474] ^ cw[477] ^ cw[480] ^ cw[484] ^ cw[487] ^ cw[489] ^ cw[490] ^ cw[492] ^ cw[493] ^ cw[496] ^ cw[498] ^ cw[499] ^ cw[502] ^ cw[505] ^ cw[508] ^ cw[509] ^ cw[520];
    assign syndrome[9] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[35] ^ cw[37] ^ cw[39] ^ cw[42] ^ cw[46] ^ cw[51] ^ cw[56] ^ cw[58] ^ cw[60] ^ cw[63] ^ cw[67] ^ cw[72] ^ cw[78] ^ cw[84] ^ cw[86] ^ cw[88] ^ cw[91] ^ cw[95] ^ cw[100] ^ cw[106] ^ cw[113] ^ cw[120] ^ cw[122] ^ cw[124] ^ cw[127] ^ cw[131] ^ cw[136] ^ cw[142] ^ cw[149] ^ cw[157] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[179] ^ cw[180] ^ cw[182] ^ cw[184] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[194] ^ cw[195] ^ cw[197] ^ cw[199] ^ cw[201] ^ cw[202] ^ cw[204] ^ cw[205] ^ cw[207] ^ cw[209] ^ cw[211] ^ cw[213] ^ cw[215] ^ cw[218] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[229] ^ cw[230] ^ cw[232] ^ cw[234] ^ cw[236] ^ cw[237] ^ cw[239] ^ cw[240] ^ cw[242] ^ cw[244] ^ cw[246] ^ cw[248] ^ cw[250] ^ cw[253] ^ cw[256] ^ cw[257] ^ cw[259] ^ cw[260] ^ cw[262] ^ cw[264] ^ cw[266] ^ cw[268] ^ cw[270] ^ cw[273] ^ cw[276] ^ cw[278] ^ cw[280] ^ cw[283] ^ cw[287] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[295] ^ cw[296] ^ cw[297] ^ cw[299] ^ cw[300] ^ cw[302] ^ cw[304] ^ cw[306] ^ cw[307] ^ cw[309] ^ cw[310] ^ cw[312] ^ cw[314] ^ cw[316] ^ cw[318] ^ cw[320] ^ cw[323] ^ cw[326] ^ cw[327] ^ cw[329] ^ cw[330] ^ cw[332] ^ cw[334] ^ cw[336] ^ cw[338] ^ cw[340] ^ cw[343] ^ cw[346] ^ cw[348] ^ cw[350] ^ cw[353] ^ cw[357] ^ cw[361] ^ cw[362] ^ cw[364] ^ cw[365] ^ cw[367] ^ cw[369] ^ cw[371] ^ cw[373] ^ cw[375] ^ cw[378] ^ cw[381] ^ cw[383] ^ cw[385] ^ cw[388] ^ cw[392] ^ cw[396] ^ cw[398] ^ cw[400] ^ cw[403] ^ cw[407] ^ cw[412] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[421] ^ cw[422] ^ cw[423] ^ cw[425] ^ cw[426] ^ cw[428] ^ cw[430] ^ cw[432] ^ cw[433] ^ cw[435] ^ cw[436] ^ cw[438] ^ cw[440] ^ cw[442] ^ cw[444] ^ cw[446] ^ cw[449] ^ cw[452] ^ cw[453] ^ cw[455] ^ cw[456] ^ cw[458] ^ cw[460] ^ cw[462] ^ cw[464] ^ cw[466] ^ cw[469] ^ cw[472] ^ cw[474] ^ cw[476] ^ cw[479] ^ cw[483] ^ cw[487] ^ cw[488] ^ cw[490] ^ cw[491] ^ cw[493] ^ cw[495] ^ cw[497] ^ cw[499] ^ cw[501] ^ cw[504] ^ cw[507] ^ cw[509] ^ cw[511] ^ cw[521];
    assign syndrome[10] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[38] ^ cw[41] ^ cw[45] ^ cw[50] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[62] ^ cw[66] ^ cw[71] ^ cw[77] ^ cw[84] ^ cw[85] ^ cw[87] ^ cw[90] ^ cw[94] ^ cw[99] ^ cw[105] ^ cw[112] ^ cw[120] ^ cw[121] ^ cw[123] ^ cw[126] ^ cw[130] ^ cw[135] ^ cw[141] ^ cw[148] ^ cw[156] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[180] ^ cw[181] ^ cw[183] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[195] ^ cw[196] ^ cw[198] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[205] ^ cw[206] ^ cw[208] ^ cw[211] ^ cw[212] ^ cw[214] ^ cw[217] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[230] ^ cw[231] ^ cw[233] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[240] ^ cw[241] ^ cw[243] ^ cw[246] ^ cw[247] ^ cw[249] ^ cw[252] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[260] ^ cw[261] ^ cw[263] ^ cw[266] ^ cw[267] ^ cw[269] ^ cw[272] ^ cw[276] ^ cw[277] ^ cw[279] ^ cw[282] ^ cw[286] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[300] ^ cw[301] ^ cw[303] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[310] ^ cw[311] ^ cw[313] ^ cw[316] ^ cw[317] ^ cw[319] ^ cw[322] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[330] ^ cw[331] ^ cw[333] ^ cw[336] ^ cw[337] ^ cw[339] ^ cw[342] ^ cw[346] ^ cw[347] ^ cw[349] ^ cw[352] ^ cw[356] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[365] ^ cw[366] ^ cw[368] ^ cw[371] ^ cw[372] ^ cw[374] ^ cw[377] ^ cw[381] ^ cw[382] ^ cw[384] ^ cw[387] ^ cw[391] ^ cw[396] ^ cw[397] ^ cw[399] ^ cw[402] ^ cw[406] ^ cw[411] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[420] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[426] ^ cw[427] ^ cw[429] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[436] ^ cw[437] ^ cw[439] ^ cw[442] ^ cw[443] ^ cw[445] ^ cw[448] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[456] ^ cw[457] ^ cw[459] ^ cw[462] ^ cw[463] ^ cw[465] ^ cw[468] ^ cw[472] ^ cw[473] ^ cw[475] ^ cw[478] ^ cw[482] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[491] ^ cw[492] ^ cw[494] ^ cw[497] ^ cw[498] ^ cw[500] ^ cw[503] ^ cw[507] ^ cw[508] ^ cw[510] ^ cw[522];
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
    assign syndrome[0] = cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[682] ^ cw[683] ^ cw[684] ^ cw[685] ^ cw[686] ^ cw[687] ^ cw[688] ^ cw[689] ^ cw[690] ^ cw[691] ^ cw[692] ^ cw[693] ^ cw[694] ^ cw[695] ^ cw[696] ^ cw[697] ^ cw[698] ^ cw[699] ^ cw[700] ^ cw[701] ^ cw[702] ^ cw[703] ^ cw[704] ^ cw[705] ^ cw[706] ^ cw[707] ^ cw[708] ^ cw[709] ^ cw[710] ^ cw[711] ^ cw[712] ^ cw[713] ^ cw[714] ^ cw[715] ^ cw[716] ^ cw[717] ^ cw[718] ^ cw[719] ^ cw[720] ^ cw[721] ^ cw[722] ^ cw[723] ^ cw[724] ^ cw[725] ^ cw[726] ^ cw[727] ^ cw[728] ^ cw[729] ^ cw[730] ^ cw[731] ^ cw[732] ^ cw[733] ^ cw[734] ^ cw[735] ^ cw[736] ^ cw[737] ^ cw[738] ^ cw[739] ^ cw[740] ^ cw[741] ^ cw[742] ^ cw[743] ^ cw[744] ^ cw[745] ^ cw[746] ^ cw[747] ^ cw[748] ^ cw[749] ^ cw[750] ^ cw[751] ^ cw[752] ^ cw[753] ^ cw[754] ^ cw[755] ^ cw[756] ^ cw[757] ^ cw[758] ^ cw[759] ^ cw[760] ^ cw[761] ^ cw[762] ^ cw[763] ^ cw[764] ^ cw[765] ^ cw[766] ^ cw[767] ^ cw[768] ^ cw[769] ^ cw[770] ^ cw[771] ^ cw[772] ^ cw[773] ^ cw[774] ^ cw[775] ^ cw[776] ^ cw[777] ^ cw[778] ^ cw[779] ^ cw[780] ^ cw[781] ^ cw[782] ^ cw[783] ^ cw[784] ^ cw[785] ^ cw[786] ^ cw[787] ^ cw[788] ^ cw[789] ^ cw[790] ^ cw[791] ^ cw[792] ^ cw[793] ^ cw[794] ^ cw[795] ^ cw[796] ^ cw[797] ^ cw[798] ^ cw[799] ^ cw[800] ^ cw[801] ^ cw[802] ^ cw[803] ^ cw[804] ^ cw[805] ^ cw[806] ^ cw[807] ^ cw[808] ^ cw[809] ^ cw[810] ^ cw[811] ^ cw[812] ^ cw[813] ^ cw[814] ^ cw[815] ^ cw[816] ^ cw[817] ^ cw[818] ^ cw[819] ^ cw[820] ^ cw[821] ^ cw[822] ^ cw[823] ^ cw[824] ^ cw[825] ^ cw[826] ^ cw[827] ^ cw[828] ^ cw[829] ^ cw[830] ^ cw[831] ^ cw[832] ^ cw[833] ^ cw[834] ^ cw[835] ^ cw[836] ^ cw[837] ^ cw[838] ^ cw[839] ^ cw[840] ^ cw[841] ^ cw[842] ^ cw[843] ^ cw[844] ^ cw[845] ^ cw[846] ^ cw[847] ^ cw[848] ^ cw[849] ^ cw[850] ^ cw[851] ^ cw[852] ^ cw[853] ^ cw[854] ^ cw[855] ^ cw[856] ^ cw[857] ^ cw[858] ^ cw[859] ^ cw[860] ^ cw[861] ^ cw[862] ^ cw[863] ^ cw[864] ^ cw[865] ^ cw[866] ^ cw[867] ^ cw[868] ^ cw[869] ^ cw[870] ^ cw[871] ^ cw[872] ^ cw[873] ^ cw[874] ^ cw[875] ^ cw[876] ^ cw[877] ^ cw[878] ^ cw[879] ^ cw[880] ^ cw[881] ^ cw[882] ^ cw[883] ^ cw[884] ^ cw[885] ^ cw[886] ^ cw[887] ^ cw[888] ^ cw[889] ^ cw[890] ^ cw[891] ^ cw[892] ^ cw[893] ^ cw[894] ^ cw[895] ^ cw[896] ^ cw[897] ^ cw[898] ^ cw[899] ^ cw[900] ^ cw[901] ^ cw[902] ^ cw[903] ^ cw[904] ^ cw[905] ^ cw[906] ^ cw[907] ^ cw[908] ^ cw[909] ^ cw[910] ^ cw[911] ^ cw[912] ^ cw[913] ^ cw[914] ^ cw[915] ^ cw[916] ^ cw[917] ^ cw[918] ^ cw[919] ^ cw[920] ^ cw[921] ^ cw[922] ^ cw[923] ^ cw[924] ^ cw[925] ^ cw[926] ^ cw[927] ^ cw[928] ^ cw[929] ^ cw[930] ^ cw[931] ^ cw[932] ^ cw[933] ^ cw[934] ^ cw[935] ^ cw[936] ^ cw[937] ^ cw[938] ^ cw[939] ^ cw[940] ^ cw[941] ^ cw[942] ^ cw[943] ^ cw[944] ^ cw[945] ^ cw[946] ^ cw[947] ^ cw[948] ^ cw[949] ^ cw[950] ^ cw[951] ^ cw[952] ^ cw[953] ^ cw[954] ^ cw[955] ^ cw[956] ^ cw[957] ^ cw[958] ^ cw[959] ^ cw[960] ^ cw[961] ^ cw[962] ^ cw[963] ^ cw[964] ^ cw[965] ^ cw[966] ^ cw[967] ^ cw[968] ^ cw[969] ^ cw[970] ^ cw[971] ^ cw[972] ^ cw[973] ^ cw[974] ^ cw[975] ^ cw[976] ^ cw[977] ^ cw[978] ^ cw[979] ^ cw[980] ^ cw[981] ^ cw[982] ^ cw[983] ^ cw[984] ^ cw[985] ^ cw[986] ^ cw[987] ^ cw[988] ^ cw[989] ^ cw[990] ^ cw[991] ^ cw[992] ^ cw[993] ^ cw[994] ^ cw[995] ^ cw[996] ^ cw[997] ^ cw[998] ^ cw[999] ^ cw[1000] ^ cw[1001] ^ cw[1002] ^ cw[1003] ^ cw[1004] ^ cw[1005] ^ cw[1006] ^ cw[1007] ^ cw[1008] ^ cw[1009] ^ cw[1010] ^ cw[1011] ^ cw[1024];
    assign syndrome[1] = cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[511] ^ cw[512] ^ cw[513] ^ cw[514] ^ cw[515] ^ cw[516] ^ cw[517] ^ cw[518] ^ cw[519] ^ cw[520] ^ cw[521] ^ cw[522] ^ cw[523] ^ cw[524] ^ cw[525] ^ cw[526] ^ cw[527] ^ cw[528] ^ cw[529] ^ cw[530] ^ cw[531] ^ cw[532] ^ cw[533] ^ cw[534] ^ cw[535] ^ cw[536] ^ cw[537] ^ cw[538] ^ cw[539] ^ cw[540] ^ cw[541] ^ cw[542] ^ cw[543] ^ cw[544] ^ cw[545] ^ cw[546] ^ cw[547] ^ cw[548] ^ cw[549] ^ cw[550] ^ cw[551] ^ cw[552] ^ cw[553] ^ cw[554] ^ cw[555] ^ cw[556] ^ cw[557] ^ cw[558] ^ cw[559] ^ cw[560] ^ cw[561] ^ cw[562] ^ cw[563] ^ cw[564] ^ cw[565] ^ cw[566] ^ cw[567] ^ cw[568] ^ cw[569] ^ cw[570] ^ cw[571] ^ cw[572] ^ cw[573] ^ cw[574] ^ cw[575] ^ cw[576] ^ cw[577] ^ cw[578] ^ cw[579] ^ cw[580] ^ cw[581] ^ cw[582] ^ cw[583] ^ cw[584] ^ cw[585] ^ cw[586] ^ cw[587] ^ cw[588] ^ cw[589] ^ cw[590] ^ cw[591] ^ cw[592] ^ cw[593] ^ cw[594] ^ cw[595] ^ cw[596] ^ cw[597] ^ cw[598] ^ cw[599] ^ cw[600] ^ cw[601] ^ cw[602] ^ cw[603] ^ cw[604] ^ cw[605] ^ cw[606] ^ cw[607] ^ cw[608] ^ cw[609] ^ cw[610] ^ cw[611] ^ cw[612] ^ cw[613] ^ cw[614] ^ cw[615] ^ cw[616] ^ cw[617] ^ cw[618] ^ cw[619] ^ cw[620] ^ cw[621] ^ cw[622] ^ cw[623] ^ cw[624] ^ cw[625] ^ cw[626] ^ cw[627] ^ cw[628] ^ cw[629] ^ cw[630] ^ cw[631] ^ cw[632] ^ cw[633] ^ cw[634] ^ cw[635] ^ cw[636] ^ cw[637] ^ cw[638] ^ cw[639] ^ cw[640] ^ cw[641] ^ cw[642] ^ cw[643] ^ cw[644] ^ cw[645] ^ cw[646] ^ cw[647] ^ cw[648] ^ cw[649] ^ cw[650] ^ cw[651] ^ cw[652] ^ cw[653] ^ cw[654] ^ cw[655] ^ cw[656] ^ cw[657] ^ cw[658] ^ cw[659] ^ cw[660] ^ cw[661] ^ cw[662] ^ cw[663] ^ cw[664] ^ cw[665] ^ cw[666] ^ cw[667] ^ cw[668] ^ cw[669] ^ cw[670] ^ cw[671] ^ cw[672] ^ cw[673] ^ cw[674] ^ cw[675] ^ cw[676] ^ cw[677] ^ cw[678] ^ cw[679] ^ cw[680] ^ cw[681] ^ cw[892] ^ cw[893] ^ cw[894] ^ cw[895] ^ cw[896] ^ cw[897] ^ cw[898] ^ cw[899] ^ cw[900] ^ cw[901] ^ cw[902] ^ cw[903] ^ cw[904] ^ cw[905] ^ cw[906] ^ cw[907] ^ cw[908] ^ cw[909] ^ cw[910] ^ cw[911] ^ cw[912] ^ cw[913] ^ cw[914] ^ cw[915] ^ cw[916] ^ cw[917] ^ cw[918] ^ cw[919] ^ cw[920] ^ cw[921] ^ cw[922] ^ cw[923] ^ cw[924] ^ cw[925] ^ cw[926] ^ cw[927] ^ cw[928] ^ cw[929] ^ cw[930] ^ cw[931] ^ cw[932] ^ cw[933] ^ cw[934] ^ cw[935] ^ cw[936] ^ cw[937] ^ cw[938] ^ cw[939] ^ cw[940] ^ cw[941] ^ cw[942] ^ cw[943] ^ cw[944] ^ cw[945] ^ cw[946] ^ cw[947] ^ cw[948] ^ cw[949] ^ cw[950] ^ cw[951] ^ cw[952] ^ cw[953] ^ cw[954] ^ cw[955] ^ cw[956] ^ cw[957] ^ cw[958] ^ cw[959] ^ cw[960] ^ cw[961] ^ cw[962] ^ cw[963] ^ cw[964] ^ cw[965] ^ cw[966] ^ cw[967] ^ cw[968] ^ cw[969] ^ cw[970] ^ cw[971] ^ cw[972] ^ cw[973] ^ cw[974] ^ cw[975] ^ cw[976] ^ cw[977] ^ cw[978] ^ cw[979] ^ cw[980] ^ cw[981] ^ cw[982] ^ cw[983] ^ cw[984] ^ cw[985] ^ cw[986] ^ cw[987] ^ cw[988] ^ cw[989] ^ cw[990] ^ cw[991] ^ cw[992] ^ cw[993] ^ cw[994] ^ cw[995] ^ cw[996] ^ cw[997] ^ cw[998] ^ cw[999] ^ cw[1000] ^ cw[1001] ^ cw[1002] ^ cw[1003] ^ cw[1004] ^ cw[1005] ^ cw[1006] ^ cw[1007] ^ cw[1008] ^ cw[1009] ^ cw[1010] ^ cw[1011] ^ cw[1025];
    assign syndrome[2] = cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[219] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[416] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[420] ^ cw[421] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[598] ^ cw[599] ^ cw[600] ^ cw[601] ^ cw[602] ^ cw[603] ^ cw[604] ^ cw[605] ^ cw[606] ^ cw[607] ^ cw[608] ^ cw[609] ^ cw[610] ^ cw[611] ^ cw[612] ^ cw[613] ^ cw[614] ^ cw[615] ^ cw[616] ^ cw[617] ^ cw[618] ^ cw[619] ^ cw[620] ^ cw[621] ^ cw[622] ^ cw[623] ^ cw[624] ^ cw[625] ^ cw[626] ^ cw[627] ^ cw[628] ^ cw[629] ^ cw[630] ^ cw[631] ^ cw[632] ^ cw[633] ^ cw[634] ^ cw[635] ^ cw[636] ^ cw[637] ^ cw[638] ^ cw[639] ^ cw[640] ^ cw[641] ^ cw[642] ^ cw[643] ^ cw[644] ^ cw[645] ^ cw[646] ^ cw[647] ^ cw[648] ^ cw[649] ^ cw[650] ^ cw[651] ^ cw[652] ^ cw[653] ^ cw[654] ^ cw[655] ^ cw[656] ^ cw[657] ^ cw[658] ^ cw[659] ^ cw[660] ^ cw[661] ^ cw[662] ^ cw[663] ^ cw[664] ^ cw[665] ^ cw[666] ^ cw[667] ^ cw[668] ^ cw[669] ^ cw[670] ^ cw[671] ^ cw[672] ^ cw[673] ^ cw[674] ^ cw[675] ^ cw[676] ^ cw[677] ^ cw[678] ^ cw[679] ^ cw[680] ^ cw[681] ^ cw[808] ^ cw[809] ^ cw[810] ^ cw[811] ^ cw[812] ^ cw[813] ^ cw[814] ^ cw[815] ^ cw[816] ^ cw[817] ^ cw[818] ^ cw[819] ^ cw[820] ^ cw[821] ^ cw[822] ^ cw[823] ^ cw[824] ^ cw[825] ^ cw[826] ^ cw[827] ^ cw[828] ^ cw[829] ^ cw[830] ^ cw[831] ^ cw[832] ^ cw[833] ^ cw[834] ^ cw[835] ^ cw[836] ^ cw[837] ^ cw[838] ^ cw[839] ^ cw[840] ^ cw[841] ^ cw[842] ^ cw[843] ^ cw[844] ^ cw[845] ^ cw[846] ^ cw[847] ^ cw[848] ^ cw[849] ^ cw[850] ^ cw[851] ^ cw[852] ^ cw[853] ^ cw[854] ^ cw[855] ^ cw[856] ^ cw[857] ^ cw[858] ^ cw[859] ^ cw[860] ^ cw[861] ^ cw[862] ^ cw[863] ^ cw[864] ^ cw[865] ^ cw[866] ^ cw[867] ^ cw[868] ^ cw[869] ^ cw[870] ^ cw[871] ^ cw[872] ^ cw[873] ^ cw[874] ^ cw[875] ^ cw[876] ^ cw[877] ^ cw[878] ^ cw[879] ^ cw[880] ^ cw[881] ^ cw[882] ^ cw[883] ^ cw[884] ^ cw[885] ^ cw[886] ^ cw[887] ^ cw[888] ^ cw[889] ^ cw[890] ^ cw[891] ^ cw[976] ^ cw[977] ^ cw[978] ^ cw[979] ^ cw[980] ^ cw[981] ^ cw[982] ^ cw[983] ^ cw[984] ^ cw[985] ^ cw[986] ^ cw[987] ^ cw[988] ^ cw[989] ^ cw[990] ^ cw[991] ^ cw[992] ^ cw[993] ^ cw[994] ^ cw[995] ^ cw[996] ^ cw[997] ^ cw[998] ^ cw[999] ^ cw[1000] ^ cw[1001] ^ cw[1002] ^ cw[1003] ^ cw[1004] ^ cw[1005] ^ cw[1006] ^ cw[1007] ^ cw[1008] ^ cw[1009] ^ cw[1010] ^ cw[1011] ^ cw[1026];
    assign syndrome[3] = cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[164] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[209] ^ cw[218] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[295] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[416] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[420] ^ cw[421] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[451] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[542] ^ cw[543] ^ cw[544] ^ cw[545] ^ cw[546] ^ cw[547] ^ cw[548] ^ cw[549] ^ cw[550] ^ cw[551] ^ cw[552] ^ cw[553] ^ cw[554] ^ cw[555] ^ cw[556] ^ cw[557] ^ cw[558] ^ cw[559] ^ cw[560] ^ cw[561] ^ cw[562] ^ cw[563] ^ cw[564] ^ cw[565] ^ cw[566] ^ cw[567] ^ cw[568] ^ cw[569] ^ cw[570] ^ cw[571] ^ cw[572] ^ cw[573] ^ cw[574] ^ cw[575] ^ cw[576] ^ cw[577] ^ cw[578] ^ cw[579] ^ cw[580] ^ cw[581] ^ cw[582] ^ cw[583] ^ cw[584] ^ cw[585] ^ cw[586] ^ cw[587] ^ cw[588] ^ cw[589] ^ cw[590] ^ cw[591] ^ cw[592] ^ cw[593] ^ cw[594] ^ cw[595] ^ cw[596] ^ cw[597] ^ cw[654] ^ cw[655] ^ cw[656] ^ cw[657] ^ cw[658] ^ cw[659] ^ cw[660] ^ cw[661] ^ cw[662] ^ cw[663] ^ cw[664] ^ cw[665] ^ cw[666] ^ cw[667] ^ cw[668] ^ cw[669] ^ cw[670] ^ cw[671] ^ cw[672] ^ cw[673] ^ cw[674] ^ cw[675] ^ cw[676] ^ cw[677] ^ cw[678] ^ cw[679] ^ cw[680] ^ cw[681] ^ cw[752] ^ cw[753] ^ cw[754] ^ cw[755] ^ cw[756] ^ cw[757] ^ cw[758] ^ cw[759] ^ cw[760] ^ cw[761] ^ cw[762] ^ cw[763] ^ cw[764] ^ cw[765] ^ cw[766] ^ cw[767] ^ cw[768] ^ cw[769] ^ cw[770] ^ cw[771] ^ cw[772] ^ cw[773] ^ cw[774] ^ cw[775] ^ cw[776] ^ cw[777] ^ cw[778] ^ cw[779] ^ cw[780] ^ cw[781] ^ cw[782] ^ cw[783] ^ cw[784] ^ cw[785] ^ cw[786] ^ cw[787] ^ cw[788] ^ cw[789] ^ cw[790] ^ cw[791] ^ cw[792] ^ cw[793] ^ cw[794] ^ cw[795] ^ cw[796] ^ cw[797] ^ cw[798] ^ cw[799] ^ cw[800] ^ cw[801] ^ cw[802] ^ cw[803] ^ cw[804] ^ cw[805] ^ cw[806] ^ cw[807] ^ cw[864] ^ cw[865] ^ cw[866] ^ cw[867] ^ cw[868] ^ cw[869] ^ cw[870] ^ cw[871] ^ cw[872] ^ cw[873] ^ cw[874] ^ cw[875] ^ cw[876] ^ cw[877] ^ cw[878] ^ cw[879] ^ cw[880] ^ cw[881] ^ cw[882] ^ cw[883] ^ cw[884] ^ cw[885] ^ cw[886] ^ cw[887] ^ cw[888] ^ cw[889] ^ cw[890] ^ cw[891] ^ cw[948] ^ cw[949] ^ cw[950] ^ cw[951] ^ cw[952] ^ cw[953] ^ cw[954] ^ cw[955] ^ cw[956] ^ cw[957] ^ cw[958] ^ cw[959] ^ cw[960] ^ cw[961] ^ cw[962] ^ cw[963] ^ cw[964] ^ cw[965] ^ cw[966] ^ cw[967] ^ cw[968] ^ cw[969] ^ cw[970] ^ cw[971] ^ cw[972] ^ cw[973] ^ cw[974] ^ cw[975] ^ cw[1004] ^ cw[1005] ^ cw[1006] ^ cw[1007] ^ cw[1008] ^ cw[1009] ^ cw[1010] ^ cw[1011] ^ cw[1020] ^ cw[1021] ^ cw[1022] ^ cw[1023] ^ cw[1027];
    assign syndrome[4] = cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[119] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[155] ^ cw[163] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[200] ^ cw[208] ^ cw[217] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[315] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[451] ^ cw[452] ^ cw[453] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[511] ^ cw[512] ^ cw[513] ^ cw[514] ^ cw[515] ^ cw[516] ^ cw[517] ^ cw[518] ^ cw[519] ^ cw[520] ^ cw[521] ^ cw[522] ^ cw[523] ^ cw[524] ^ cw[525] ^ cw[526] ^ cw[527] ^ cw[528] ^ cw[529] ^ cw[530] ^ cw[531] ^ cw[532] ^ cw[533] ^ cw[534] ^ cw[535] ^ cw[536] ^ cw[537] ^ cw[538] ^ cw[539] ^ cw[540] ^ cw[541] ^ cw[577] ^ cw[578] ^ cw[579] ^ cw[580] ^ cw[581] ^ cw[582] ^ cw[583] ^ cw[584] ^ cw[585] ^ cw[586] ^ cw[587] ^ cw[588] ^ cw[589] ^ cw[590] ^ cw[591] ^ cw[592] ^ cw[593] ^ cw[594] ^ cw[595] ^ cw[596] ^ cw[597] ^ cw[633] ^ cw[634] ^ cw[635] ^ cw[636] ^ cw[637] ^ cw[638] ^ cw[639] ^ cw[640] ^ cw[641] ^ cw[642] ^ cw[643] ^ cw[644] ^ cw[645] ^ cw[646] ^ cw[647] ^ cw[648] ^ cw[649] ^ cw[650] ^ cw[651] ^ cw[652] ^ cw[653] ^ cw[675] ^ cw[676] ^ cw[677] ^ cw[678] ^ cw[679] ^ cw[680] ^ cw[681] ^ cw[717] ^ cw[718] ^ cw[719] ^ cw[720] ^ cw[721] ^ cw[722] ^ cw[723] ^ cw[724] ^ cw[725] ^ cw[726] ^ cw[727] ^ cw[728] ^ cw[729] ^ cw[730] ^ cw[731] ^ cw[732] ^ cw[733] ^ cw[734] ^ cw[735] ^ cw[736] ^ cw[737] ^ cw[738] ^ cw[739] ^ cw[740] ^ cw[741] ^ cw[742] ^ cw[743] ^ cw[744] ^ cw[745] ^ cw[746] ^ cw[747] ^ cw[748] ^ cw[749] ^ cw[750] ^ cw[751] ^ cw[787] ^ cw[788] ^ cw[789] ^ cw[790] ^ cw[791] ^ cw[792] ^ cw[793] ^ cw[794] ^ cw[795] ^ cw[796] ^ cw[797] ^ cw[798] ^ cw[799] ^ cw[800] ^ cw[801] ^ cw[802] ^ cw[803] ^ cw[804] ^ cw[805] ^ cw[806] ^ cw[807] ^ cw[843] ^ cw[844] ^ cw[845] ^ cw[846] ^ cw[847] ^ cw[848] ^ cw[849] ^ cw[850] ^ cw[851] ^ cw[852] ^ cw[853] ^ cw[854] ^ cw[855] ^ cw[856] ^ cw[857] ^ cw[858] ^ cw[859] ^ cw[860] ^ cw[861] ^ cw[862] ^ cw[863] ^ cw[885] ^ cw[886] ^ cw[887] ^ cw[888] ^ cw[889] ^ cw[890] ^ cw[891] ^ cw[927] ^ cw[928] ^ cw[929] ^ cw[930] ^ cw[931] ^ cw[932] ^ cw[933] ^ cw[934] ^ cw[935] ^ cw[936] ^ cw[937] ^ cw[938] ^ cw[939] ^ cw[940] ^ cw[941] ^ cw[942] ^ cw[943] ^ cw[944] ^ cw[945] ^ cw[946] ^ cw[947] ^ cw[969] ^ cw[970] ^ cw[971] ^ cw[972] ^ cw[973] ^ cw[974] ^ cw[975] ^ cw[997] ^ cw[998] ^ cw[999] ^ cw[1000] ^ cw[1001] ^ cw[1002] ^ cw[1003] ^ cw[1011] ^ cw[1013] ^ cw[1014] ^ cw[1015] ^ cw[1016] ^ cw[1017] ^ cw[1018] ^ cw[1019] ^ cw[1028];
    assign syndrome[5] = cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[83] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[111] ^ cw[118] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[147] ^ cw[154] ^ cw[162] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[192] ^ cw[199] ^ cw[207] ^ cw[216] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[295] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[331] ^ cw[332] ^ cw[333] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[401] ^ cw[402] ^ cw[403] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[436] ^ cw[437] ^ cw[438] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[466] ^ cw[467] ^ cw[468] ^ cw[469] ^ cw[470] ^ cw[471] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[527] ^ cw[528] ^ cw[529] ^ cw[530] ^ cw[531] ^ cw[532] ^ cw[533] ^ cw[534] ^ cw[535] ^ cw[536] ^ cw[537] ^ cw[538] ^ cw[539] ^ cw[540] ^ cw[541] ^ cw[562] ^ cw[563] ^ cw[564] ^ cw[565] ^ cw[566] ^ cw[567] ^ cw[568] ^ cw[569] ^ cw[570] ^ cw[571] ^ cw[572] ^ cw[573] ^ cw[574] ^ cw[575] ^ cw[576] ^ cw[592] ^ cw[593] ^ cw[594] ^ cw[595] ^ cw[596] ^ cw[597] ^ cw[618] ^ cw[619] ^ cw[620] ^ cw[621] ^ cw[622] ^ cw[623] ^ cw[624] ^ cw[625] ^ cw[626] ^ cw[627] ^ cw[628] ^ cw[629] ^ cw[630] ^ cw[631] ^ cw[632] ^ cw[648] ^ cw[649] ^ cw[650] ^ cw[651] ^ cw[652] ^ cw[653] ^ cw[669] ^ cw[670] ^ cw[671] ^ cw[672] ^ cw[673] ^ cw[674] ^ cw[681] ^ cw[697] ^ cw[698] ^ cw[699] ^ cw[700] ^ cw[701] ^ cw[702] ^ cw[703] ^ cw[704] ^ cw[705] ^ cw[706] ^ cw[707] ^ cw[708] ^ cw[709] ^ cw[710] ^ cw[711] ^ cw[712] ^ cw[713] ^ cw[714] ^ cw[715] ^ cw[716] ^ cw[737] ^ cw[738] ^ cw[739] ^ cw[740] ^ cw[741] ^ cw[742] ^ cw[743] ^ cw[744] ^ cw[745] ^ cw[746] ^ cw[747] ^ cw[748] ^ cw[749] ^ cw[750] ^ cw[751] ^ cw[772] ^ cw[773] ^ cw[774] ^ cw[775] ^ cw[776] ^ cw[777] ^ cw[778] ^ cw[779] ^ cw[780] ^ cw[781] ^ cw[782] ^ cw[783] ^ cw[784] ^ cw[785] ^ cw[786] ^ cw[802] ^ cw[803] ^ cw[804] ^ cw[805] ^ cw[806] ^ cw[807] ^ cw[828] ^ cw[829] ^ cw[830] ^ cw[831] ^ cw[832] ^ cw[833] ^ cw[834] ^ cw[835] ^ cw[836] ^ cw[837] ^ cw[838] ^ cw[839] ^ cw[840] ^ cw[841] ^ cw[842] ^ cw[858] ^ cw[859] ^ cw[860] ^ cw[861] ^ cw[862] ^ cw[863] ^ cw[879] ^ cw[880] ^ cw[881] ^ cw[882] ^ cw[883] ^ cw[884] ^ cw[891] ^ cw[912] ^ cw[913] ^ cw[914] ^ cw[915] ^ cw[916] ^ cw[917] ^ cw[918] ^ cw[919] ^ cw[920] ^ cw[921] ^ cw[922] ^ cw[923] ^ cw[924] ^ cw[925] ^ cw[926] ^ cw[942] ^ cw[943] ^ cw[944] ^ cw[945] ^ cw[946] ^ cw[947] ^ cw[963] ^ cw[964] ^ cw[965] ^ cw[966] ^ cw[967] ^ cw[968] ^ cw[975] ^ cw[991] ^ cw[992] ^ cw[993] ^ cw[994] ^ cw[995] ^ cw[996] ^ cw[1003] ^ cw[1010] ^ cw[1012] ^ cw[1014] ^ cw[1015] ^ cw[1016] ^ cw[1017] ^ cw[1018] ^ cw[1019] ^ cw[1021] ^ cw[1022] ^ cw[1023] ^ cw[1029];
    assign syndrome[6] = cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[55] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[76] ^ cw[82] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[104] ^ cw[110] ^ cw[117] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[140] ^ cw[146] ^ cw[153] ^ cw[161] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[185] ^ cw[191] ^ cw[198] ^ cw[206] ^ cw[215] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[266] ^ cw[267] ^ cw[268] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[301] ^ cw[302] ^ cw[303] ^ cw[304] ^ cw[305] ^ cw[306] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[321] ^ cw[322] ^ cw[323] ^ cw[324] ^ cw[325] ^ cw[326] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[341] ^ cw[342] ^ cw[343] ^ cw[344] ^ cw[345] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[371] ^ cw[372] ^ cw[373] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[391] ^ cw[392] ^ cw[393] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[411] ^ cw[412] ^ cw[413] ^ cw[414] ^ cw[415] ^ cw[426] ^ cw[427] ^ cw[428] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[446] ^ cw[447] ^ cw[448] ^ cw[449] ^ cw[450] ^ cw[461] ^ cw[462] ^ cw[463] ^ cw[464] ^ cw[465] ^ cw[471] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[497] ^ cw[498] ^ cw[499] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[517] ^ cw[518] ^ cw[519] ^ cw[520] ^ cw[521] ^ cw[522] ^ cw[523] ^ cw[524] ^ cw[525] ^ cw[526] ^ cw[537] ^ cw[538] ^ cw[539] ^ cw[540] ^ cw[541] ^ cw[552] ^ cw[553] ^ cw[554] ^ cw[555] ^ cw[556] ^ cw[557] ^ cw[558] ^ cw[559] ^ cw[560] ^ cw[561] ^ cw[572] ^ cw[573] ^ cw[574] ^ cw[575] ^ cw[576] ^ cw[587] ^ cw[588] ^ cw[589] ^ cw[590] ^ cw[591] ^ cw[597] ^ cw[608] ^ cw[609] ^ cw[610] ^ cw[611] ^ cw[612] ^ cw[613] ^ cw[614] ^ cw[615] ^ cw[616] ^ cw[617] ^ cw[628] ^ cw[629] ^ cw[630] ^ cw[631] ^ cw[632] ^ cw[643] ^ cw[644] ^ cw[645] ^ cw[646] ^ cw[647] ^ cw[653] ^ cw[664] ^ cw[665] ^ cw[666] ^ cw[667] ^ cw[668] ^ cw[674] ^ cw[680] ^ cw[687] ^ cw[688] ^ cw[689] ^ cw[690] ^ cw[691] ^ cw[692] ^ cw[693] ^ cw[694] ^ cw[695] ^ cw[696] ^ cw[707] ^ cw[708] ^ cw[709] ^ cw[710] ^ cw[711] ^ cw[712] ^ cw[713] ^ cw[714] ^ cw[715] ^ cw[716] ^ cw[727] ^ cw[728] ^ cw[729] ^ cw[730] ^ cw[731] ^ cw[732] ^ cw[733] ^ cw[734] ^ cw[735] ^ cw[736] ^ cw[747] ^ cw[748] ^ cw[749] ^ cw[750] ^ cw[751] ^ cw[762] ^ cw[763] ^ cw[764] ^ cw[765] ^ cw[766] ^ cw[767] ^ cw[768] ^ cw[769] ^ cw[770] ^ cw[771] ^ cw[782] ^ cw[783] ^ cw[784] ^ cw[785] ^ cw[786] ^ cw[797] ^ cw[798] ^ cw[799] ^ cw[800] ^ cw[801] ^ cw[807] ^ cw[818] ^ cw[819] ^ cw[820] ^ cw[821] ^ cw[822] ^ cw[823] ^ cw[824] ^ cw[825] ^ cw[826] ^ cw[827] ^ cw[838] ^ cw[839] ^ cw[840] ^ cw[841] ^ cw[842] ^ cw[853] ^ cw[854] ^ cw[855] ^ cw[856] ^ cw[857] ^ cw[863] ^ cw[874] ^ cw[875] ^ cw[876] ^ cw[877] ^ cw[878] ^ cw[884] ^ cw[890] ^ cw[902] ^ cw[903] ^ cw[904] ^ cw[905] ^ cw[906] ^ cw[907] ^ cw[908] ^ cw[909] ^ cw[910] ^ cw[911] ^ cw[922] ^ cw[923] ^ cw[924] ^ cw[925] ^ cw[926] ^ cw[937] ^ cw[938] ^ cw[939] ^ cw[940] ^ cw[941] ^ cw[947] ^ cw[958] ^ cw[959] ^ cw[960] ^ cw[961] ^ cw[962] ^ cw[968] ^ cw[974] ^ cw[986] ^ cw[987] ^ cw[988] ^ cw[989] ^ cw[990] ^ cw[996] ^ cw[1002] ^ cw[1009] ^ cw[1012] ^ cw[1013] ^ cw[1015] ^ cw[1016] ^ cw[1017] ^ cw[1018] ^ cw[1019] ^ cw[1020] ^ cw[1022] ^ cw[1023] ^ cw[1030];
    assign syndrome[7] = cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[34] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[70] ^ cw[75] ^ cw[81] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[98] ^ cw[103] ^ cw[109] ^ cw[116] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[134] ^ cw[139] ^ cw[145] ^ cw[152] ^ cw[160] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[179] ^ cw[184] ^ cw[190] ^ cw[197] ^ cw[205] ^ cw[214] ^ cw[220] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[260] ^ cw[261] ^ cw[262] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[272] ^ cw[273] ^ cw[274] ^ cw[275] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[285] ^ cw[286] ^ cw[287] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[295] ^ cw[296] ^ cw[297] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[307] ^ cw[308] ^ cw[309] ^ cw[310] ^ cw[315] ^ cw[316] ^ cw[317] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[327] ^ cw[328] ^ cw[329] ^ cw[330] ^ cw[337] ^ cw[338] ^ cw[339] ^ cw[340] ^ cw[345] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[355] ^ cw[356] ^ cw[357] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[365] ^ cw[366] ^ cw[367] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[377] ^ cw[378] ^ cw[379] ^ cw[380] ^ cw[385] ^ cw[386] ^ cw[387] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[397] ^ cw[398] ^ cw[399] ^ cw[400] ^ cw[407] ^ cw[408] ^ cw[409] ^ cw[410] ^ cw[415] ^ cw[420] ^ cw[421] ^ cw[422] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[432] ^ cw[433] ^ cw[434] ^ cw[435] ^ cw[442] ^ cw[443] ^ cw[444] ^ cw[445] ^ cw[450] ^ cw[457] ^ cw[458] ^ cw[459] ^ cw[460] ^ cw[465] ^ cw[470] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[481] ^ cw[482] ^ cw[483] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[491] ^ cw[492] ^ cw[493] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[503] ^ cw[504] ^ cw[505] ^ cw[506] ^ cw[511] ^ cw[512] ^ cw[513] ^ cw[514] ^ cw[515] ^ cw[516] ^ cw[523] ^ cw[524] ^ cw[525] ^ cw[526] ^ cw[533] ^ cw[534] ^ cw[535] ^ cw[536] ^ cw[541] ^ cw[546] ^ cw[547] ^ cw[548] ^ cw[549] ^ cw[550] ^ cw[551] ^ cw[558] ^ cw[559] ^ cw[560] ^ cw[561] ^ cw[568] ^ cw[569] ^ cw[570] ^ cw[571] ^ cw[576] ^ cw[583] ^ cw[584] ^ cw[585] ^ cw[586] ^ cw[591] ^ cw[596] ^ cw[602] ^ cw[603] ^ cw[604] ^ cw[605] ^ cw[606] ^ cw[607] ^ cw[614] ^ cw[615] ^ cw[616] ^ cw[617] ^ cw[624] ^ cw[625] ^ cw[626] ^ cw[627] ^ cw[632] ^ cw[639] ^ cw[640] ^ cw[641] ^ cw[642] ^ cw[647] ^ cw[652] ^ cw[660] ^ cw[661] ^ cw[662] ^ cw[663] ^ cw[668] ^ cw[673] ^ cw[679] ^ cw[683] ^ cw[684] ^ cw[685] ^ cw[686] ^ cw[691] ^ cw[692] ^ cw[693] ^ cw[694] ^ cw[695] ^ cw[696] ^ cw[701] ^ cw[702] ^ cw[703] ^ cw[704] ^ cw[705] ^ cw[706] ^ cw[713] ^ cw[714] ^ cw[715] ^ cw[716] ^ cw[721] ^ cw[722] ^ cw[723] ^ cw[724] ^ cw[725] ^ cw[726] ^ cw[733] ^ cw[734] ^ cw[735] ^ cw[736] ^ cw[743] ^ cw[744] ^ cw[745] ^ cw[746] ^ cw[751] ^ cw[756] ^ cw[757] ^ cw[758] ^ cw[759] ^ cw[760] ^ cw[761] ^ cw[768] ^ cw[769] ^ cw[770] ^ cw[771] ^ cw[778] ^ cw[779] ^ cw[780] ^ cw[781] ^ cw[786] ^ cw[793] ^ cw[794] ^ cw[795] ^ cw[796] ^ cw[801] ^ cw[806] ^ cw[812] ^ cw[813] ^ cw[814] ^ cw[815] ^ cw[816] ^ cw[817] ^ cw[824] ^ cw[825] ^ cw[826] ^ cw[827] ^ cw[834] ^ cw[835] ^ cw[836] ^ cw[837] ^ cw[842] ^ cw[849] ^ cw[850] ^ cw[851] ^ cw[852] ^ cw[857] ^ cw[862] ^ cw[870] ^ cw[871] ^ cw[872] ^ cw[873] ^ cw[878] ^ cw[883] ^ cw[889] ^ cw[896] ^ cw[897] ^ cw[898] ^ cw[899] ^ cw[900] ^ cw[901] ^ cw[908] ^ cw[909] ^ cw[910] ^ cw[911] ^ cw[918] ^ cw[919] ^ cw[920] ^ cw[921] ^ cw[926] ^ cw[933] ^ cw[934] ^ cw[935] ^ cw[936] ^ cw[941] ^ cw[946] ^ cw[954] ^ cw[955] ^ cw[956] ^ cw[957] ^ cw[962] ^ cw[967] ^ cw[973] ^ cw[982] ^ cw[983] ^ cw[984] ^ cw[985] ^ cw[990] ^ cw[995] ^ cw[1001] ^ cw[1008] ^ cw[1012] ^ cw[1013] ^ cw[1014] ^ cw[1016] ^ cw[1017] ^ cw[1018] ^ cw[1019] ^ cw[1020] ^ cw[1021] ^ cw[1023] ^ cw[1031];
    assign syndrome[8] = cw[1] ^ cw[2] ^ cw[3] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[33] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[44] ^ cw[48] ^ cw[53] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[65] ^ cw[69] ^ cw[74] ^ cw[80] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[93] ^ cw[97] ^ cw[102] ^ cw[108] ^ cw[115] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[129] ^ cw[133] ^ cw[138] ^ cw[144] ^ cw[151] ^ cw[159] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[174] ^ cw[178] ^ cw[183] ^ cw[189] ^ cw[196] ^ cw[204] ^ cw[213] ^ cw[220] ^ cw[221] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[257] ^ cw[258] ^ cw[259] ^ cw[263] ^ cw[264] ^ cw[265] ^ cw[269] ^ cw[270] ^ cw[271] ^ cw[275] ^ cw[276] ^ cw[278] ^ cw[279] ^ cw[280] ^ cw[282] ^ cw[283] ^ cw[284] ^ cw[288] ^ cw[289] ^ cw[290] ^ cw[292] ^ cw[293] ^ cw[294] ^ cw[298] ^ cw[299] ^ cw[300] ^ cw[304] ^ cw[305] ^ cw[306] ^ cw[310] ^ cw[312] ^ cw[313] ^ cw[314] ^ cw[318] ^ cw[319] ^ cw[320] ^ cw[324] ^ cw[325] ^ cw[326] ^ cw[330] ^ cw[334] ^ cw[335] ^ cw[336] ^ cw[340] ^ cw[344] ^ cw[346] ^ cw[348] ^ cw[349] ^ cw[350] ^ cw[352] ^ cw[353] ^ cw[354] ^ cw[358] ^ cw[359] ^ cw[360] ^ cw[362] ^ cw[363] ^ cw[364] ^ cw[368] ^ cw[369] ^ cw[370] ^ cw[374] ^ cw[375] ^ cw[376] ^ cw[380] ^ cw[382] ^ cw[383] ^ cw[384] ^ cw[388] ^ cw[389] ^ cw[390] ^ cw[394] ^ cw[395] ^ cw[396] ^ cw[400] ^ cw[404] ^ cw[405] ^ cw[406] ^ cw[410] ^ cw[414] ^ cw[417] ^ cw[418] ^ cw[419] ^ cw[423] ^ cw[424] ^ cw[425] ^ cw[429] ^ cw[430] ^ cw[431] ^ cw[435] ^ cw[439] ^ cw[440] ^ cw[441] ^ cw[445] ^ cw[449] ^ cw[454] ^ cw[455] ^ cw[456] ^ cw[460] ^ cw[464] ^ cw[469] ^ cw[472] ^ cw[474] ^ cw[475] ^ cw[476] ^ cw[478] ^ cw[479] ^ cw[480] ^ cw[484] ^ cw[485] ^ cw[486] ^ cw[488] ^ cw[489] ^ cw[490] ^ cw[494] ^ cw[495] ^ cw[496] ^ cw[500] ^ cw[501] ^ cw[502] ^ cw[506] ^ cw[508] ^ cw[509] ^ cw[510] ^ cw[514] ^ cw[515] ^ cw[516] ^ cw[520] ^ cw[521] ^ cw[522] ^ cw[526] ^ cw[530] ^ cw[531] ^ cw[532] ^ cw[536] ^ cw[540] ^ cw[543] ^ cw[544] ^ cw[545] ^ cw[549] ^ cw[550] ^ cw[551] ^ cw[555] ^ cw[556] ^ cw[557] ^ cw[561] ^ cw[565] ^ cw[566] ^ cw[567] ^ cw[571] ^ cw[575] ^ cw[580] ^ cw[581] ^ cw[582] ^ cw[586] ^ cw[590] ^ cw[595] ^ cw[599] ^ cw[600] ^ cw[601] ^ cw[605] ^ cw[606] ^ cw[607] ^ cw[611] ^ cw[612] ^ cw[613] ^ cw[617] ^ cw[621] ^ cw[622] ^ cw[623] ^ cw[627] ^ cw[631] ^ cw[636] ^ cw[637] ^ cw[638] ^ cw[642] ^ cw[646] ^ cw[651] ^ cw[657] ^ cw[658] ^ cw[659] ^ cw[663] ^ cw[667] ^ cw[672] ^ cw[678] ^ cw[682] ^ cw[684] ^ cw[685] ^ cw[686] ^ cw[688] ^ cw[689] ^ cw[690] ^ cw[694] ^ cw[695] ^ cw[696] ^ cw[698] ^ cw[699] ^ cw[700] ^ cw[704] ^ cw[705] ^ cw[706] ^ cw[710] ^ cw[711] ^ cw[712] ^ cw[716] ^ cw[718] ^ cw[719] ^ cw[720] ^ cw[724] ^ cw[725] ^ cw[726] ^ cw[730] ^ cw[731] ^ cw[732] ^ cw[736] ^ cw[740] ^ cw[741] ^ cw[742] ^ cw[746] ^ cw[750] ^ cw[753] ^ cw[754] ^ cw[755] ^ cw[759] ^ cw[760] ^ cw[761] ^ cw[765] ^ cw[766] ^ cw[767] ^ cw[771] ^ cw[775] ^ cw[776] ^ cw[777] ^ cw[781] ^ cw[785] ^ cw[790] ^ cw[791] ^ cw[792] ^ cw[796] ^ cw[800] ^ cw[805] ^ cw[809] ^ cw[810] ^ cw[811] ^ cw[815] ^ cw[816] ^ cw[817] ^ cw[821] ^ cw[822] ^ cw[823] ^ cw[827] ^ cw[831] ^ cw[832] ^ cw[833] ^ cw[837] ^ cw[841] ^ cw[846] ^ cw[847] ^ cw[848] ^ cw[852] ^ cw[856] ^ cw[861] ^ cw[867] ^ cw[868] ^ cw[869] ^ cw[873] ^ cw[877] ^ cw[882] ^ cw[888] ^ cw[893] ^ cw[894] ^ cw[895] ^ cw[899] ^ cw[900] ^ cw[901] ^ cw[905] ^ cw[906] ^ cw[907] ^ cw[911] ^ cw[915] ^ cw[916] ^ cw[917] ^ cw[921] ^ cw[925] ^ cw[930] ^ cw[931] ^ cw[932] ^ cw[936] ^ cw[940] ^ cw[945] ^ cw[951] ^ cw[952] ^ cw[953] ^ cw[957] ^ cw[961] ^ cw[966] ^ cw[972] ^ cw[979] ^ cw[980] ^ cw[981] ^ cw[985] ^ cw[989] ^ cw[994] ^ cw[1000] ^ cw[1007] ^ cw[1012] ^ cw[1013] ^ cw[1014] ^ cw[1015] ^ cw[1017] ^ cw[1018] ^ cw[1019] ^ cw[1020] ^ cw[1021] ^ cw[1022] ^ cw[1032];
    assign syndrome[9] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[9] ^ cw[11] ^ cw[12] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[28] ^ cw[32] ^ cw[36] ^ cw[37] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[52] ^ cw[57] ^ cw[58] ^ cw[61] ^ cw[64] ^ cw[68] ^ cw[73] ^ cw[79] ^ cw[85] ^ cw[86] ^ cw[89] ^ cw[92] ^ cw[96] ^ cw[101] ^ cw[107] ^ cw[114] ^ cw[121] ^ cw[122] ^ cw[125] ^ cw[128] ^ cw[132] ^ cw[137] ^ cw[143] ^ cw[150] ^ cw[158] ^ cw[166] ^ cw[167] ^ cw[170] ^ cw[173] ^ cw[177] ^ cw[182] ^ cw[188] ^ cw[195] ^ cw[203] ^ cw[212] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[233] ^ cw[234] ^ cw[236] ^ cw[237] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[248] ^ cw[249] ^ cw[251] ^ cw[252] ^ cw[255] ^ cw[256] ^ cw[258] ^ cw[259] ^ cw[261] ^ cw[262] ^ cw[265] ^ cw[267] ^ cw[268] ^ cw[271] ^ cw[274] ^ cw[276] ^ cw[277] ^ cw[279] ^ cw[280] ^ cw[281] ^ cw[283] ^ cw[284] ^ cw[286] ^ cw[287] ^ cw[290] ^ cw[291] ^ cw[293] ^ cw[294] ^ cw[296] ^ cw[297] ^ cw[300] ^ cw[302] ^ cw[303] ^ cw[306] ^ cw[309] ^ cw[311] ^ cw[313] ^ cw[314] ^ cw[316] ^ cw[317] ^ cw[320] ^ cw[322] ^ cw[323] ^ cw[326] ^ cw[329] ^ cw[332] ^ cw[333] ^ cw[336] ^ cw[339] ^ cw[343] ^ cw[346] ^ cw[347] ^ cw[349] ^ cw[350] ^ cw[351] ^ cw[353] ^ cw[354] ^ cw[356] ^ cw[357] ^ cw[360] ^ cw[361] ^ cw[363] ^ cw[364] ^ cw[366] ^ cw[367] ^ cw[370] ^ cw[372] ^ cw[373] ^ cw[376] ^ cw[379] ^ cw[381] ^ cw[383] ^ cw[384] ^ cw[386] ^ cw[387] ^ cw[390] ^ cw[392] ^ cw[393] ^ cw[396] ^ cw[399] ^ cw[402] ^ cw[403] ^ cw[406] ^ cw[409] ^ cw[413] ^ cw[416] ^ cw[418] ^ cw[419] ^ cw[421] ^ cw[422] ^ cw[425] ^ cw[427] ^ cw[428] ^ cw[431] ^ cw[434] ^ cw[437] ^ cw[438] ^ cw[441] ^ cw[444] ^ cw[448] ^ cw[452] ^ cw[453] ^ cw[456] ^ cw[459] ^ cw[463] ^ cw[468] ^ cw[472] ^ cw[473] ^ cw[475] ^ cw[476] ^ cw[477] ^ cw[479] ^ cw[480] ^ cw[482] ^ cw[483] ^ cw[486] ^ cw[487] ^ cw[489] ^ cw[490] ^ cw[492] ^ cw[493] ^ cw[496] ^ cw[498] ^ cw[499] ^ cw[502] ^ cw[505] ^ cw[507] ^ cw[509] ^ cw[510] ^ cw[512] ^ cw[513] ^ cw[516] ^ cw[518] ^ cw[519] ^ cw[522] ^ cw[525] ^ cw[528] ^ cw[529] ^ cw[532] ^ cw[535] ^ cw[539] ^ cw[542] ^ cw[544] ^ cw[545] ^ cw[547] ^ cw[548] ^ cw[551] ^ cw[553] ^ cw[554] ^ cw[557] ^ cw[560] ^ cw[563] ^ cw[564] ^ cw[567] ^ cw[570] ^ cw[574] ^ cw[578] ^ cw[579] ^ cw[582] ^ cw[585] ^ cw[589] ^ cw[594] ^ cw[598] ^ cw[600] ^ cw[601] ^ cw[603] ^ cw[604] ^ cw[607] ^ cw[609] ^ cw[610] ^ cw[613] ^ cw[616] ^ cw[619] ^ cw[620] ^ cw[623] ^ cw[626] ^ cw[630] ^ cw[634] ^ cw[635] ^ cw[638] ^ cw[641] ^ cw[645] ^ cw[650] ^ cw[655] ^ cw[656] ^ cw[659] ^ cw[662] ^ cw[666] ^ cw[671] ^ cw[677] ^ cw[682] ^ cw[683] ^ cw[685] ^ cw[686] ^ cw[687] ^ cw[689] ^ cw[690] ^ cw[692] ^ cw[693] ^ cw[696] ^ cw[697] ^ cw[699] ^ cw[700] ^ cw[702] ^ cw[703] ^ cw[706] ^ cw[708] ^ cw[709] ^ cw[712] ^ cw[715] ^ cw[717] ^ cw[719] ^ cw[720] ^ cw[722] ^ cw[723] ^ cw[726] ^ cw[728] ^ cw[729] ^ cw[732] ^ cw[735] ^ cw[738] ^ cw[739] ^ cw[742] ^ cw[745] ^ cw[749] ^ cw[752] ^ cw[754] ^ cw[755] ^ cw[757] ^ cw[758] ^ cw[761] ^ cw[763] ^ cw[764] ^ cw[767] ^ cw[770] ^ cw[773] ^ cw[774] ^ cw[777] ^ cw[780] ^ cw[784] ^ cw[788] ^ cw[789] ^ cw[792] ^ cw[795] ^ cw[799] ^ cw[804] ^ cw[808] ^ cw[810] ^ cw[811] ^ cw[813] ^ cw[814] ^ cw[817] ^ cw[819] ^ cw[820] ^ cw[823] ^ cw[826] ^ cw[829] ^ cw[830] ^ cw[833] ^ cw[836] ^ cw[840] ^ cw[844] ^ cw[845] ^ cw[848] ^ cw[851] ^ cw[855] ^ cw[860] ^ cw[865] ^ cw[866] ^ cw[869] ^ cw[872] ^ cw[876] ^ cw[881] ^ cw[887] ^ cw[892] ^ cw[894] ^ cw[895] ^ cw[897] ^ cw[898] ^ cw[901] ^ cw[903] ^ cw[904] ^ cw[907] ^ cw[910] ^ cw[913] ^ cw[914] ^ cw[917] ^ cw[920] ^ cw[924] ^ cw[928] ^ cw[929] ^ cw[932] ^ cw[935] ^ cw[939] ^ cw[944] ^ cw[949] ^ cw[950] ^ cw[953] ^ cw[956] ^ cw[960] ^ cw[965] ^ cw[971] ^ cw[977] ^ cw[978] ^ cw[981] ^ cw[984] ^ cw[988] ^ cw[993] ^ cw[999] ^ cw[1006] ^ cw[1012] ^ cw[1013] ^ cw[1014] ^ cw[1015] ^ cw[1016] ^ cw[1018] ^ cw[1019] ^ cw[1020] ^ cw[1021] ^ cw[1022] ^ cw[1023] ^ cw[1033];
    assign syndrome[10] = cw[0] ^ cw[1] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[8] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[27] ^ cw[31] ^ cw[35] ^ cw[37] ^ cw[39] ^ cw[42] ^ cw[46] ^ cw[51] ^ cw[56] ^ cw[58] ^ cw[60] ^ cw[63] ^ cw[67] ^ cw[72] ^ cw[78] ^ cw[84] ^ cw[86] ^ cw[88] ^ cw[91] ^ cw[95] ^ cw[100] ^ cw[106] ^ cw[113] ^ cw[120] ^ cw[122] ^ cw[124] ^ cw[127] ^ cw[131] ^ cw[136] ^ cw[142] ^ cw[149] ^ cw[157] ^ cw[165] ^ cw[167] ^ cw[169] ^ cw[172] ^ cw[176] ^ cw[181] ^ cw[187] ^ cw[194] ^ cw[202] ^ cw[211] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[234] ^ cw[235] ^ cw[237] ^ cw[239] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[249] ^ cw[250] ^ cw[252] ^ cw[254] ^ cw[256] ^ cw[257] ^ cw[259] ^ cw[260] ^ cw[262] ^ cw[264] ^ cw[266] ^ cw[268] ^ cw[270] ^ cw[273] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[280] ^ cw[281] ^ cw[282] ^ cw[284] ^ cw[285] ^ cw[287] ^ cw[289] ^ cw[291] ^ cw[292] ^ cw[294] ^ cw[295] ^ cw[297] ^ cw[299] ^ cw[301] ^ cw[303] ^ cw[305] ^ cw[308] ^ cw[311] ^ cw[312] ^ cw[314] ^ cw[315] ^ cw[317] ^ cw[319] ^ cw[321] ^ cw[323] ^ cw[325] ^ cw[328] ^ cw[331] ^ cw[333] ^ cw[335] ^ cw[338] ^ cw[342] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[350] ^ cw[351] ^ cw[352] ^ cw[354] ^ cw[355] ^ cw[357] ^ cw[359] ^ cw[361] ^ cw[362] ^ cw[364] ^ cw[365] ^ cw[367] ^ cw[369] ^ cw[371] ^ cw[373] ^ cw[375] ^ cw[378] ^ cw[381] ^ cw[382] ^ cw[384] ^ cw[385] ^ cw[387] ^ cw[389] ^ cw[391] ^ cw[393] ^ cw[395] ^ cw[398] ^ cw[401] ^ cw[403] ^ cw[405] ^ cw[408] ^ cw[412] ^ cw[416] ^ cw[417] ^ cw[419] ^ cw[420] ^ cw[422] ^ cw[424] ^ cw[426] ^ cw[428] ^ cw[430] ^ cw[433] ^ cw[436] ^ cw[438] ^ cw[440] ^ cw[443] ^ cw[447] ^ cw[451] ^ cw[453] ^ cw[455] ^ cw[458] ^ cw[462] ^ cw[467] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[476] ^ cw[477] ^ cw[478] ^ cw[480] ^ cw[481] ^ cw[483] ^ cw[485] ^ cw[487] ^ cw[488] ^ cw[490] ^ cw[491] ^ cw[493] ^ cw[495] ^ cw[497] ^ cw[499] ^ cw[501] ^ cw[504] ^ cw[507] ^ cw[508] ^ cw[510] ^ cw[511] ^ cw[513] ^ cw[515] ^ cw[517] ^ cw[519] ^ cw[521] ^ cw[524] ^ cw[527] ^ cw[529] ^ cw[531] ^ cw[534] ^ cw[538] ^ cw[542] ^ cw[543] ^ cw[545] ^ cw[546] ^ cw[548] ^ cw[550] ^ cw[552] ^ cw[554] ^ cw[556] ^ cw[559] ^ cw[562] ^ cw[564] ^ cw[566] ^ cw[569] ^ cw[573] ^ cw[577] ^ cw[579] ^ cw[581] ^ cw[584] ^ cw[588] ^ cw[593] ^ cw[598] ^ cw[599] ^ cw[601] ^ cw[602] ^ cw[604] ^ cw[606] ^ cw[608] ^ cw[610] ^ cw[612] ^ cw[615] ^ cw[618] ^ cw[620] ^ cw[622] ^ cw[625] ^ cw[629] ^ cw[633] ^ cw[635] ^ cw[637] ^ cw[640] ^ cw[644] ^ cw[649] ^ cw[654] ^ cw[656] ^ cw[658] ^ cw[661] ^ cw[665] ^ cw[670] ^ cw[676] ^ cw[682] ^ cw[683] ^ cw[684] ^ cw[686] ^ cw[687] ^ cw[688] ^ cw[690] ^ cw[691] ^ cw[693] ^ cw[695] ^ cw[697] ^ cw[698] ^ cw[700] ^ cw[701] ^ cw[703] ^ cw[705] ^ cw[707] ^ cw[709] ^ cw[711] ^ cw[714] ^ cw[717] ^ cw[718] ^ cw[720] ^ cw[721] ^ cw[723] ^ cw[725] ^ cw[727] ^ cw[729] ^ cw[731] ^ cw[734] ^ cw[737] ^ cw[739] ^ cw[741] ^ cw[744] ^ cw[748] ^ cw[752] ^ cw[753] ^ cw[755] ^ cw[756] ^ cw[758] ^ cw[760] ^ cw[762] ^ cw[764] ^ cw[766] ^ cw[769] ^ cw[772] ^ cw[774] ^ cw[776] ^ cw[779] ^ cw[783] ^ cw[787] ^ cw[789] ^ cw[791] ^ cw[794] ^ cw[798] ^ cw[803] ^ cw[808] ^ cw[809] ^ cw[811] ^ cw[812] ^ cw[814] ^ cw[816] ^ cw[818] ^ cw[820] ^ cw[822] ^ cw[825] ^ cw[828] ^ cw[830] ^ cw[832] ^ cw[835] ^ cw[839] ^ cw[843] ^ cw[845] ^ cw[847] ^ cw[850] ^ cw[854] ^ cw[859] ^ cw[864] ^ cw[866] ^ cw[868] ^ cw[871] ^ cw[875] ^ cw[880] ^ cw[886] ^ cw[892] ^ cw[893] ^ cw[895] ^ cw[896] ^ cw[898] ^ cw[900] ^ cw[902] ^ cw[904] ^ cw[906] ^ cw[909] ^ cw[912] ^ cw[914] ^ cw[916] ^ cw[919] ^ cw[923] ^ cw[927] ^ cw[929] ^ cw[931] ^ cw[934] ^ cw[938] ^ cw[943] ^ cw[948] ^ cw[950] ^ cw[952] ^ cw[955] ^ cw[959] ^ cw[964] ^ cw[970] ^ cw[976] ^ cw[978] ^ cw[980] ^ cw[983] ^ cw[987] ^ cw[992] ^ cw[998] ^ cw[1005] ^ cw[1012] ^ cw[1013] ^ cw[1014] ^ cw[1015] ^ cw[1016] ^ cw[1017] ^ cw[1019] ^ cw[1020] ^ cw[1021] ^ cw[1022] ^ cw[1023] ^ cw[1034];
    assign syndrome[11] = cw[0] ^ cw[1] ^ cw[2] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[16] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[26] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[38] ^ cw[41] ^ cw[45] ^ cw[50] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[62] ^ cw[66] ^ cw[71] ^ cw[77] ^ cw[84] ^ cw[85] ^ cw[87] ^ cw[90] ^ cw[94] ^ cw[99] ^ cw[105] ^ cw[112] ^ cw[120] ^ cw[121] ^ cw[123] ^ cw[126] ^ cw[130] ^ cw[135] ^ cw[141] ^ cw[148] ^ cw[156] ^ cw[165] ^ cw[166] ^ cw[168] ^ cw[171] ^ cw[175] ^ cw[180] ^ cw[186] ^ cw[193] ^ cw[201] ^ cw[210] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[235] ^ cw[236] ^ cw[238] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[250] ^ cw[251] ^ cw[253] ^ cw[256] ^ cw[257] ^ cw[258] ^ cw[260] ^ cw[261] ^ cw[263] ^ cw[266] ^ cw[267] ^ cw[269] ^ cw[272] ^ cw[276] ^ cw[277] ^ cw[278] ^ cw[279] ^ cw[281] ^ cw[282] ^ cw[283] ^ cw[285] ^ cw[286] ^ cw[288] ^ cw[291] ^ cw[292] ^ cw[293] ^ cw[295] ^ cw[296] ^ cw[298] ^ cw[301] ^ cw[302] ^ cw[304] ^ cw[307] ^ cw[311] ^ cw[312] ^ cw[313] ^ cw[315] ^ cw[316] ^ cw[318] ^ cw[321] ^ cw[322] ^ cw[324] ^ cw[327] ^ cw[331] ^ cw[332] ^ cw[334] ^ cw[337] ^ cw[341] ^ cw[346] ^ cw[347] ^ cw[348] ^ cw[349] ^ cw[351] ^ cw[352] ^ cw[353] ^ cw[355] ^ cw[356] ^ cw[358] ^ cw[361] ^ cw[362] ^ cw[363] ^ cw[365] ^ cw[366] ^ cw[368] ^ cw[371] ^ cw[372] ^ cw[374] ^ cw[377] ^ cw[381] ^ cw[382] ^ cw[383] ^ cw[385] ^ cw[386] ^ cw[388] ^ cw[391] ^ cw[392] ^ cw[394] ^ cw[397] ^ cw[401] ^ cw[402] ^ cw[404] ^ cw[407] ^ cw[411] ^ cw[416] ^ cw[417] ^ cw[418] ^ cw[420] ^ cw[421] ^ cw[423] ^ cw[426] ^ cw[427] ^ cw[429] ^ cw[432] ^ cw[436] ^ cw[437] ^ cw[439] ^ cw[442] ^ cw[446] ^ cw[451] ^ cw[452] ^ cw[454] ^ cw[457] ^ cw[461] ^ cw[466] ^ cw[472] ^ cw[473] ^ cw[474] ^ cw[475] ^ cw[477] ^ cw[478] ^ cw[479] ^ cw[481] ^ cw[482] ^ cw[484] ^ cw[487] ^ cw[488] ^ cw[489] ^ cw[491] ^ cw[492] ^ cw[494] ^ cw[497] ^ cw[498] ^ cw[500] ^ cw[503] ^ cw[507] ^ cw[508] ^ cw[509] ^ cw[511] ^ cw[512] ^ cw[514] ^ cw[517] ^ cw[518] ^ cw[520] ^ cw[523] ^ cw[527] ^ cw[528] ^ cw[530] ^ cw[533] ^ cw[537] ^ cw[542] ^ cw[543] ^ cw[544] ^ cw[546] ^ cw[547] ^ cw[549] ^ cw[552] ^ cw[553] ^ cw[555] ^ cw[558] ^ cw[562] ^ cw[563] ^ cw[565] ^ cw[568] ^ cw[572] ^ cw[577] ^ cw[578] ^ cw[580] ^ cw[583] ^ cw[587] ^ cw[592] ^ cw[598] ^ cw[599] ^ cw[600] ^ cw[602] ^ cw[603] ^ cw[605] ^ cw[608] ^ cw[609] ^ cw[611] ^ cw[614] ^ cw[618] ^ cw[619] ^ cw[621] ^ cw[624] ^ cw[628] ^ cw[633] ^ cw[634] ^ cw[636] ^ cw[639] ^ cw[643] ^ cw[648] ^ cw[654] ^ cw[655] ^ cw[657] ^ cw[660] ^ cw[664] ^ cw[669] ^ cw[675] ^ cw[682] ^ cw[683] ^ cw[684] ^ cw[685] ^ cw[687] ^ cw[688] ^ cw[689] ^ cw[691] ^ cw[692] ^ cw[694] ^ cw[697] ^ cw[698] ^ cw[699] ^ cw[701] ^ cw[702] ^ cw[704] ^ cw[707] ^ cw[708] ^ cw[710] ^ cw[713] ^ cw[717] ^ cw[718] ^ cw[719] ^ cw[721] ^ cw[722] ^ cw[724] ^ cw[727] ^ cw[728] ^ cw[730] ^ cw[733] ^ cw[737] ^ cw[738] ^ cw[740] ^ cw[743] ^ cw[747] ^ cw[752] ^ cw[753] ^ cw[754] ^ cw[756] ^ cw[757] ^ cw[759] ^ cw[762] ^ cw[763] ^ cw[765] ^ cw[768] ^ cw[772] ^ cw[773] ^ cw[775] ^ cw[778] ^ cw[782] ^ cw[787] ^ cw[788] ^ cw[790] ^ cw[793] ^ cw[797] ^ cw[802] ^ cw[808] ^ cw[809] ^ cw[810] ^ cw[812] ^ cw[813] ^ cw[815] ^ cw[818] ^ cw[819] ^ cw[821] ^ cw[824] ^ cw[828] ^ cw[829] ^ cw[831] ^ cw[834] ^ cw[838] ^ cw[843] ^ cw[844] ^ cw[846] ^ cw[849] ^ cw[853] ^ cw[858] ^ cw[864] ^ cw[865] ^ cw[867] ^ cw[870] ^ cw[874] ^ cw[879] ^ cw[885] ^ cw[892] ^ cw[893] ^ cw[894] ^ cw[896] ^ cw[897] ^ cw[899] ^ cw[902] ^ cw[903] ^ cw[905] ^ cw[908] ^ cw[912] ^ cw[913] ^ cw[915] ^ cw[918] ^ cw[922] ^ cw[927] ^ cw[928] ^ cw[930] ^ cw[933] ^ cw[937] ^ cw[942] ^ cw[948] ^ cw[949] ^ cw[951] ^ cw[954] ^ cw[958] ^ cw[963] ^ cw[969] ^ cw[976] ^ cw[977] ^ cw[979] ^ cw[982] ^ cw[986] ^ cw[991] ^ cw[997] ^ cw[1004] ^ cw[1012] ^ cw[1013] ^ cw[1014] ^ cw[1015] ^ cw[1016] ^ cw[1017] ^ cw[1018] ^ cw[1020] ^ cw[1021] ^ cw[1022] ^ cw[1023] ^ cw[1035];
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
      .NumStages(RegisterSyndrome),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_syndrome (
      .clk,
      .rst,
      .in_valid(rcv_valid_d),
      .in({cw, syndrome}),
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
  logic internal_error_ce;
  assign internal_error_ce =
    internal_error_syndrome_is_odd && (internal_h_column_match != '0);

  //------
  // Correct the codeword (if necessary and possible), then extract the message and data.
  //------
  // If there was a DUE, then the corr codeword is still corrupted and
  // the message and data are likely to also be corrupted.

  logic [CodewordWidth-1:0] internal_corrected_codeword;

  assign internal_corrected_codeword = internal_codeword ^ internal_h_column_match;

  `BR_ASSERT_IMPL(internal_h_column_match_onehot0_a,
                  internal_valid |-> $onehot0(internal_h_column_match))
  `BR_ASSERT_IMPL(due_no_h_column_match_a,
                  internal_valid && internal_error_due |->
                  (internal_h_column_match == '0))
  `BR_ASSERT_IMPL(no_error_correction_a,
                  internal_valid && !internal_error_ce |->
                  (internal_corrected_codeword == internal_codeword))
  `BR_ASSERT_IMPL(error_correction_a,
                  internal_valid && internal_error_ce |->
                  (internal_corrected_codeword != internal_codeword))

  //------
  // Optionally register the output signals.
  //------
  logic [InputWidth-1:0] internal_corrected_codeword_compressed;
  assign `BR_INSERT_TO_MSB(internal_corrected_codeword_compressed, internal_corrected_codeword[CodewordWidth-1 -: ParityWidth])
  assign `BR_INSERT_TO_LSB(internal_corrected_codeword_compressed, internal_corrected_codeword[DataWidth-1:0])
  if (CodewordWidth > InputWidth) begin : gen_internal_corrected_codeword_unused
    `BR_UNUSED_NAMED(unused_internal_corrected_codeword, internal_corrected_codeword[MessageWidth-1 : DataWidth])
  end
  br_delay_valid #(
      .Width(InputWidth + 2 + ParityWidth),
      .NumStages(RegisterOutputs == 1 ? 1 : 0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_outputs (
      .clk,
      .rst,
      .in_valid(internal_valid),
      .in({internal_corrected_codeword_compressed,
          internal_error_ce,
          internal_error_due,
          internal_error_syndrome}),
      .out_valid(dec_valid),
      .out({dec_codeword,
            dec_error_ce,
            dec_error_due,
            dec_error_syndrome}),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  // ri lint_check_waive FULL_RANGE
  assign dec_data = dec_codeword[DataWidth-1:0];

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(latency_a, rcv_valid |-> ##Latency dec_valid)
  `BR_ASSERT_IMPL(ce_due_mutually_exclusive_a,
                  dec_valid |-> $onehot0({dec_error_ce, dec_error_due}))
  `BR_COVER_IMPL(ce_c, dec_valid && dec_error_ce)
  `BR_COVER_IMPL(due_c, dec_valid && dec_error_due)

  // verilog_format: on
  // verilog_lint: waive-stop line-length

endmodule : br_ecc_secded_decoder
