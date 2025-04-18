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
// Any DataWidth >= 4 is supported, up to a maximum of 256.
// * If DataWidth is a power of 2, it benefits from a specifically generated ECC code construction
//   and the MessageWidth is set to the DataWidth.
// * If DataWidth is not a power of 2, it is treated as internally zero-padded up to the nearest
//   supported MessageWidth before it is decoded.
//
// The following table outlines the supported configurations. [x,y] notation indicates
// an inclusive range from x to y. Notice that all power-of-2 DataWidth from 4 up to 256
// and all power-of-2 CodewordWidth from 8 up to 256 get optimal constructions.
//
// | DataWidth   | ParityWidth (r) | MessageWidth (k) | CodewordWidth (n = k + r) |
// |-------------|-----------------|------------------|---------------------------|
// | 4           | 4               | 4                | 8                         |
// | [5,8]       | 5               | 8                | 13                        |
// | [9,11]      | 5               | 11               | 16                        |
// | [12,16]     | 6               | 16               | 22                        |
// | [17,26]     | 6               | 26               | 32                        |
// | [27,32]     | 7               | 32               | 39                        |
// | [33,57]     | 7               | 57               | 64                        |
// | [58,64]     | 8               | 64               | 72                        |
// | [65,120]    | 8               | 120              | 128                       |
// | [121,128]   | 9               | 128              | 137                       |
// | [129,247]   | 9               | 247              | 256                       |
// | [248,256] * | 10 *            | 256 *            | 266 *                     |
//
// * For r=10, the maximum MessageWidth is actually 502, but solving for a Hsiao code
// this big has proven to be computationally difficult. Accordingly, we limit the maximum
// overall MessageWidth to 256.
//
// References:
// [1] https://ieeexplore.ieee.org/abstract/document/5391627

`include "br_asserts.svh"
`include "br_asserts_internal.svh"
`include "br_assign.svh"
`include "br_unused.svh"

// TODO(mgottscho): Pipeline the syndrome decoding and then correction with a parameter.
module br_ecc_secded_decoder #(
    parameter int DataWidth = 4,  // Must be at least 4
    parameter int ParityWidth = 4,  // Must be at least 4 and at most 10
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
    localparam int MessageWidth = br_ecc::get_message_width(DataWidth, ParityWidth),
    localparam int CodewordWidth = MessageWidth + ParityWidth,
    // ri lint_check_waive PARAM_NOT_USED
    localparam int Latency = RegisterInputs + RegisterSyndrome + RegisterOutputs
) (
    // Positive edge-triggered clock.
    input  logic                     clk,
    // Synchronous active-high reset.
    input  logic                     rst,

    // Decoder input (received data and parity, possibly with errors).
    // Provide the rcv_data and rcv_parity as separate signals,
    // rather than the complete rcv_codeword, because the codeword
    // construction may involve some zero-padded bits that aren't necessary
    // to transmit through the faulty communication channel.
    //
    // The rcv_data is internally zero-padded up to the message size
    // and then concatenated with the rcv_parity to form the received
    // codeword prior to syndrome decoding.
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
  `BR_ASSERT_STATIC(data_width_gte_4_a, DataWidth >= 4)
  `BR_ASSERT_STATIC(data_width_lte_256_a, DataWidth <= 256)
  `BR_ASSERT_STATIC(parity_width_gte_4_a, ParityWidth >= 4)
  `BR_ASSERT_STATIC(parity_width_lte_12_a, ParityWidth <= 10)
  `BR_ASSERT_STATIC(data_width_fits_in_message_width_a, DataWidth <= MessageWidth)
  `BR_ASSERT_STATIC(right_sized_parity_bits_a, DataWidth > br_ecc::get_max_message_width(ParityWidth - 1))

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

  if ((CodewordWidth == 8) && (MessageWidth == 4)) begin : gen_8_4
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 4)
    assign syndrome[3] = cw[1] ^ cw[2] ^ cw[3] ^ cw[4];
    assign syndrome[2] = cw[0] ^ cw[2] ^ cw[3] ^ cw[5];
    assign syndrome[1] = cw[0] ^ cw[1] ^ cw[3] ^ cw[6];
    assign syndrome[0] = cw[0] ^ cw[1] ^ cw[2] ^ cw[7];
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
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[8];
    assign syndrome[3] = cw[0] ^ cw[1] ^ cw[2] ^ cw[6] ^ cw[7] ^ cw[9];
    assign syndrome[2] = cw[0] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[7] ^ cw[10];
    assign syndrome[1] = cw[1] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[11];
    assign syndrome[0] = cw[2] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[12];
    assign parity_check_matrix[0] = 5'b11100;
    assign parity_check_matrix[1] = 5'b11010;
    assign parity_check_matrix[2] = 5'b11001;
    assign parity_check_matrix[3] = 5'b10101;
    assign parity_check_matrix[4] = 5'b10110;
    assign parity_check_matrix[5] = 5'b00111;
    assign parity_check_matrix[6] = 5'b01011;
    assign parity_check_matrix[7] = 5'b01110;
    assign parity_check_matrix[8] = 5'b10000;
    assign parity_check_matrix[9] = 5'b01000;
    assign parity_check_matrix[10] = 5'b00100;
    assign parity_check_matrix[11] = 5'b00010;
    assign parity_check_matrix[12] = 5'b00001;
  end else if ((CodewordWidth == 16) && (MessageWidth == 11)) begin : gen_16_11
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 5)
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[10] ^ cw[11];
    assign syndrome[3] = cw[0] ^ cw[1] ^ cw[2] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[12];
    assign syndrome[2] = cw[0] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[13];
    assign syndrome[1] = cw[1] ^ cw[3] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[9] ^ cw[10] ^ cw[14];
    assign syndrome[0] = cw[2] ^ cw[3] ^ cw[4] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[10] ^ cw[15];
    assign parity_check_matrix[0] = 5'b11100;
    assign parity_check_matrix[1] = 5'b11010;
    assign parity_check_matrix[2] = 5'b11001;
    assign parity_check_matrix[3] = 5'b10011;
    assign parity_check_matrix[4] = 5'b10101;
    assign parity_check_matrix[5] = 5'b10110;
    assign parity_check_matrix[6] = 5'b00111;
    assign parity_check_matrix[7] = 5'b01011;
    assign parity_check_matrix[8] = 5'b01101;
    assign parity_check_matrix[9] = 5'b01110;
    assign parity_check_matrix[10] = 5'b11111;
    assign parity_check_matrix[11] = 5'b10000;
    assign parity_check_matrix[12] = 5'b01000;
    assign parity_check_matrix[13] = 5'b00100;
    assign parity_check_matrix[14] = 5'b00010;
    assign parity_check_matrix[15] = 5'b00001;
  end else if ((CodewordWidth == 22) && (MessageWidth == 16)) begin : gen_22_16
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 6)
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[16];
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[10] ^ cw[11] ^ cw[13] ^ cw[14] ^ cw[17];
    assign syndrome[3] = cw[0] ^ cw[4] ^ cw[5] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[18];
    assign syndrome[2] = cw[1] ^ cw[4] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[14] ^ cw[15] ^ cw[19];
    assign syndrome[1] = cw[2] ^ cw[5] ^ cw[6] ^ cw[8] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[15] ^ cw[20];
    assign syndrome[0] = cw[3] ^ cw[6] ^ cw[7] ^ cw[9] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[21];
    assign parity_check_matrix[0] = 6'b111000;
    assign parity_check_matrix[1] = 6'b110100;
    assign parity_check_matrix[2] = 6'b110010;
    assign parity_check_matrix[3] = 6'b110001;
    assign parity_check_matrix[4] = 6'b101100;
    assign parity_check_matrix[5] = 6'b101010;
    assign parity_check_matrix[6] = 6'b100011;
    assign parity_check_matrix[7] = 6'b100101;
    assign parity_check_matrix[8] = 6'b001110;
    assign parity_check_matrix[9] = 6'b001101;
    assign parity_check_matrix[10] = 6'b011100;
    assign parity_check_matrix[11] = 6'b011010;
    assign parity_check_matrix[12] = 6'b001011;
    assign parity_check_matrix[13] = 6'b010011;
    assign parity_check_matrix[14] = 6'b010101;
    assign parity_check_matrix[15] = 6'b000111;
    assign parity_check_matrix[16] = 6'b100000;
    assign parity_check_matrix[17] = 6'b010000;
    assign parity_check_matrix[18] = 6'b001000;
    assign parity_check_matrix[19] = 6'b000100;
    assign parity_check_matrix[20] = 6'b000010;
    assign parity_check_matrix[21] = 6'b000001;
  end else if ((CodewordWidth == 32) && (MessageWidth == 26)) begin : gen_32_26
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 6)
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26];
    assign syndrome[4] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[20] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[27];
    assign syndrome[3] = cw[0] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[28];
    assign syndrome[2] = cw[1] ^ cw[4] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[24] ^ cw[25] ^ cw[29];
    assign syndrome[1] = cw[2] ^ cw[5] ^ cw[7] ^ cw[9] ^ cw[11] ^ cw[13] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[25] ^ cw[30];
    assign syndrome[0] = cw[3] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[31];
    assign parity_check_matrix[0] = 6'b111000;
    assign parity_check_matrix[1] = 6'b110100;
    assign parity_check_matrix[2] = 6'b110010;
    assign parity_check_matrix[3] = 6'b110001;
    assign parity_check_matrix[4] = 6'b101100;
    assign parity_check_matrix[5] = 6'b101010;
    assign parity_check_matrix[6] = 6'b101001;
    assign parity_check_matrix[7] = 6'b100011;
    assign parity_check_matrix[8] = 6'b100101;
    assign parity_check_matrix[9] = 6'b100110;
    assign parity_check_matrix[10] = 6'b011100;
    assign parity_check_matrix[11] = 6'b011010;
    assign parity_check_matrix[12] = 6'b011001;
    assign parity_check_matrix[13] = 6'b010011;
    assign parity_check_matrix[14] = 6'b010101;
    assign parity_check_matrix[15] = 6'b010110;
    assign parity_check_matrix[16] = 6'b000111;
    assign parity_check_matrix[17] = 6'b001011;
    assign parity_check_matrix[18] = 6'b001101;
    assign parity_check_matrix[19] = 6'b001110;
    assign parity_check_matrix[20] = 6'b011111;
    assign parity_check_matrix[21] = 6'b101111;
    assign parity_check_matrix[22] = 6'b110111;
    assign parity_check_matrix[23] = 6'b111011;
    assign parity_check_matrix[24] = 6'b111101;
    assign parity_check_matrix[25] = 6'b111110;
    assign parity_check_matrix[26] = 6'b100000;
    assign parity_check_matrix[27] = 6'b010000;
    assign parity_check_matrix[28] = 6'b001000;
    assign parity_check_matrix[29] = 6'b000100;
    assign parity_check_matrix[30] = 6'b000010;
    assign parity_check_matrix[31] = 6'b000001;
  end else if ((CodewordWidth == 39) && (MessageWidth == 32)) begin : gen_39_32
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 7)
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[32];
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[33];
    assign syndrome[4] = cw[0] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[23] ^ cw[27] ^ cw[28] ^ cw[30] ^ cw[31] ^ cw[34];
    assign syndrome[3] = cw[1] ^ cw[5] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[14] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[24] ^ cw[26] ^ cw[28] ^ cw[29] ^ cw[31] ^ cw[35];
    assign syndrome[2] = cw[2] ^ cw[6] ^ cw[9] ^ cw[12] ^ cw[13] ^ cw[15] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[29] ^ cw[30] ^ cw[36];
    assign syndrome[1] = cw[3] ^ cw[7] ^ cw[10] ^ cw[13] ^ cw[16] ^ cw[19] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[37];
    assign syndrome[0] = cw[4] ^ cw[8] ^ cw[11] ^ cw[12] ^ cw[17] ^ cw[20] ^ cw[21] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[38];
    assign parity_check_matrix[0] = 7'b1110000;
    assign parity_check_matrix[1] = 7'b1101000;
    assign parity_check_matrix[2] = 7'b1100100;
    assign parity_check_matrix[3] = 7'b1100010;
    assign parity_check_matrix[4] = 7'b1100001;
    assign parity_check_matrix[5] = 7'b1011000;
    assign parity_check_matrix[6] = 7'b1010100;
    assign parity_check_matrix[7] = 7'b1010010;
    assign parity_check_matrix[8] = 7'b1010001;
    assign parity_check_matrix[9] = 7'b1001100;
    assign parity_check_matrix[10] = 7'b1001010;
    assign parity_check_matrix[11] = 7'b1001001;
    assign parity_check_matrix[12] = 7'b1000101;
    assign parity_check_matrix[13] = 7'b1000110;
    assign parity_check_matrix[14] = 7'b0111000;
    assign parity_check_matrix[15] = 7'b0110100;
    assign parity_check_matrix[16] = 7'b0110010;
    assign parity_check_matrix[17] = 7'b0110001;
    assign parity_check_matrix[18] = 7'b0101100;
    assign parity_check_matrix[19] = 7'b0101010;
    assign parity_check_matrix[20] = 7'b0101001;
    assign parity_check_matrix[21] = 7'b0100101;
    assign parity_check_matrix[22] = 7'b0100110;
    assign parity_check_matrix[23] = 7'b0010011;
    assign parity_check_matrix[24] = 7'b0001011;
    assign parity_check_matrix[25] = 7'b0000111;
    assign parity_check_matrix[26] = 7'b0001110;
    assign parity_check_matrix[27] = 7'b0010110;
    assign parity_check_matrix[28] = 7'b0011010;
    assign parity_check_matrix[29] = 7'b0001101;
    assign parity_check_matrix[30] = 7'b0010101;
    assign parity_check_matrix[31] = 7'b0011001;
    assign parity_check_matrix[32] = 7'b1000000;
    assign parity_check_matrix[33] = 7'b0100000;
    assign parity_check_matrix[34] = 7'b0010000;
    assign parity_check_matrix[35] = 7'b0001000;
    assign parity_check_matrix[36] = 7'b0000100;
    assign parity_check_matrix[37] = 7'b0000010;
    assign parity_check_matrix[38] = 7'b0000001;
  end else if ((CodewordWidth == 64) && (MessageWidth == 57)) begin : gen_64_57
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 7)
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[56] ^ cw[57];
    assign syndrome[5] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[58];
    assign syndrome[4] = cw[0] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[59];
    assign syndrome[3] = cw[1] ^ cw[5] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[15] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[60];
    assign syndrome[2] = cw[2] ^ cw[6] ^ cw[9] ^ cw[13] ^ cw[14] ^ cw[16] ^ cw[19] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[61];
    assign syndrome[1] = cw[3] ^ cw[7] ^ cw[10] ^ cw[12] ^ cw[14] ^ cw[17] ^ cw[20] ^ cw[22] ^ cw[24] ^ cw[26] ^ cw[28] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[34] ^ cw[36] ^ cw[38] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[55] ^ cw[56] ^ cw[62];
    assign syndrome[0] = cw[4] ^ cw[8] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[18] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[56] ^ cw[63];
    assign parity_check_matrix[0] = 7'b1110000;
    assign parity_check_matrix[1] = 7'b1101000;
    assign parity_check_matrix[2] = 7'b1100100;
    assign parity_check_matrix[3] = 7'b1100010;
    assign parity_check_matrix[4] = 7'b1100001;
    assign parity_check_matrix[5] = 7'b1011000;
    assign parity_check_matrix[6] = 7'b1010100;
    assign parity_check_matrix[7] = 7'b1010010;
    assign parity_check_matrix[8] = 7'b1010001;
    assign parity_check_matrix[9] = 7'b1001100;
    assign parity_check_matrix[10] = 7'b1001010;
    assign parity_check_matrix[11] = 7'b1001001;
    assign parity_check_matrix[12] = 7'b1000011;
    assign parity_check_matrix[13] = 7'b1000101;
    assign parity_check_matrix[14] = 7'b1000110;
    assign parity_check_matrix[15] = 7'b0111000;
    assign parity_check_matrix[16] = 7'b0110100;
    assign parity_check_matrix[17] = 7'b0110010;
    assign parity_check_matrix[18] = 7'b0110001;
    assign parity_check_matrix[19] = 7'b0101100;
    assign parity_check_matrix[20] = 7'b0101010;
    assign parity_check_matrix[21] = 7'b0101001;
    assign parity_check_matrix[22] = 7'b0100011;
    assign parity_check_matrix[23] = 7'b0100101;
    assign parity_check_matrix[24] = 7'b0100110;
    assign parity_check_matrix[25] = 7'b0011100;
    assign parity_check_matrix[26] = 7'b0011010;
    assign parity_check_matrix[27] = 7'b0011001;
    assign parity_check_matrix[28] = 7'b0010011;
    assign parity_check_matrix[29] = 7'b0010101;
    assign parity_check_matrix[30] = 7'b0010110;
    assign parity_check_matrix[31] = 7'b0000111;
    assign parity_check_matrix[32] = 7'b0001011;
    assign parity_check_matrix[33] = 7'b0001101;
    assign parity_check_matrix[34] = 7'b0001110;
    assign parity_check_matrix[35] = 7'b1111100;
    assign parity_check_matrix[36] = 7'b1111010;
    assign parity_check_matrix[37] = 7'b1111001;
    assign parity_check_matrix[38] = 7'b1110011;
    assign parity_check_matrix[39] = 7'b1110101;
    assign parity_check_matrix[40] = 7'b1110110;
    assign parity_check_matrix[41] = 7'b1100111;
    assign parity_check_matrix[42] = 7'b1101011;
    assign parity_check_matrix[43] = 7'b1101101;
    assign parity_check_matrix[44] = 7'b1101110;
    assign parity_check_matrix[45] = 7'b1001111;
    assign parity_check_matrix[46] = 7'b1010111;
    assign parity_check_matrix[47] = 7'b1011011;
    assign parity_check_matrix[48] = 7'b1011101;
    assign parity_check_matrix[49] = 7'b1011110;
    assign parity_check_matrix[50] = 7'b0011111;
    assign parity_check_matrix[51] = 7'b0101111;
    assign parity_check_matrix[52] = 7'b0110111;
    assign parity_check_matrix[53] = 7'b0111011;
    assign parity_check_matrix[54] = 7'b0111101;
    assign parity_check_matrix[55] = 7'b0111110;
    assign parity_check_matrix[56] = 7'b1111111;
    assign parity_check_matrix[57] = 7'b1000000;
    assign parity_check_matrix[58] = 7'b0100000;
    assign parity_check_matrix[59] = 7'b0010000;
    assign parity_check_matrix[60] = 7'b0001000;
    assign parity_check_matrix[61] = 7'b0000100;
    assign parity_check_matrix[62] = 7'b0000010;
    assign parity_check_matrix[63] = 7'b0000001;
  end else if ((CodewordWidth == 72) && (MessageWidth == 64)) begin : gen_72_64
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 8)
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[64];
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[61] ^ cw[62] ^ cw[65];
    assign syndrome[5] = cw[0] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[56] ^ cw[57] ^ cw[59] ^ cw[61] ^ cw[62] ^ cw[66];
    assign syndrome[4] = cw[1] ^ cw[6] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[21] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[56] ^ cw[58] ^ cw[59] ^ cw[61] ^ cw[63] ^ cw[67];
    assign syndrome[3] = cw[2] ^ cw[7] ^ cw[11] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[22] ^ cw[26] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[36] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[58] ^ cw[60] ^ cw[61] ^ cw[63] ^ cw[68];
    assign syndrome[2] = cw[3] ^ cw[8] ^ cw[12] ^ cw[15] ^ cw[19] ^ cw[20] ^ cw[23] ^ cw[27] ^ cw[30] ^ cw[34] ^ cw[35] ^ cw[37] ^ cw[40] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[54] ^ cw[55] ^ cw[57] ^ cw[59] ^ cw[60] ^ cw[62] ^ cw[63] ^ cw[69];
    assign syndrome[1] = cw[4] ^ cw[9] ^ cw[13] ^ cw[16] ^ cw[18] ^ cw[20] ^ cw[24] ^ cw[28] ^ cw[31] ^ cw[33] ^ cw[35] ^ cw[38] ^ cw[41] ^ cw[43] ^ cw[45] ^ cw[47] ^ cw[49] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[55] ^ cw[57] ^ cw[59] ^ cw[60] ^ cw[62] ^ cw[63] ^ cw[70];
    assign syndrome[0] = cw[5] ^ cw[10] ^ cw[14] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[25] ^ cw[29] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[39] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[58] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[71];
    assign parity_check_matrix[0] = 8'b11100000;
    assign parity_check_matrix[1] = 8'b11010000;
    assign parity_check_matrix[2] = 8'b11001000;
    assign parity_check_matrix[3] = 8'b11000100;
    assign parity_check_matrix[4] = 8'b11000010;
    assign parity_check_matrix[5] = 8'b11000001;
    assign parity_check_matrix[6] = 8'b10110000;
    assign parity_check_matrix[7] = 8'b10101000;
    assign parity_check_matrix[8] = 8'b10100100;
    assign parity_check_matrix[9] = 8'b10100010;
    assign parity_check_matrix[10] = 8'b10100001;
    assign parity_check_matrix[11] = 8'b10011000;
    assign parity_check_matrix[12] = 8'b10010100;
    assign parity_check_matrix[13] = 8'b10010010;
    assign parity_check_matrix[14] = 8'b10010001;
    assign parity_check_matrix[15] = 8'b10001100;
    assign parity_check_matrix[16] = 8'b10001010;
    assign parity_check_matrix[17] = 8'b10001001;
    assign parity_check_matrix[18] = 8'b10000011;
    assign parity_check_matrix[19] = 8'b10000101;
    assign parity_check_matrix[20] = 8'b10000110;
    assign parity_check_matrix[21] = 8'b01110000;
    assign parity_check_matrix[22] = 8'b01101000;
    assign parity_check_matrix[23] = 8'b01100100;
    assign parity_check_matrix[24] = 8'b01100010;
    assign parity_check_matrix[25] = 8'b01100001;
    assign parity_check_matrix[26] = 8'b01011000;
    assign parity_check_matrix[27] = 8'b01010100;
    assign parity_check_matrix[28] = 8'b01010010;
    assign parity_check_matrix[29] = 8'b01010001;
    assign parity_check_matrix[30] = 8'b01001100;
    assign parity_check_matrix[31] = 8'b01001010;
    assign parity_check_matrix[32] = 8'b01001001;
    assign parity_check_matrix[33] = 8'b01000011;
    assign parity_check_matrix[34] = 8'b01000101;
    assign parity_check_matrix[35] = 8'b01000110;
    assign parity_check_matrix[36] = 8'b00111000;
    assign parity_check_matrix[37] = 8'b00110100;
    assign parity_check_matrix[38] = 8'b00110010;
    assign parity_check_matrix[39] = 8'b00110001;
    assign parity_check_matrix[40] = 8'b00101100;
    assign parity_check_matrix[41] = 8'b00101010;
    assign parity_check_matrix[42] = 8'b00101001;
    assign parity_check_matrix[43] = 8'b00100011;
    assign parity_check_matrix[44] = 8'b00100101;
    assign parity_check_matrix[45] = 8'b00100110;
    assign parity_check_matrix[46] = 8'b00011100;
    assign parity_check_matrix[47] = 8'b00011010;
    assign parity_check_matrix[48] = 8'b00011001;
    assign parity_check_matrix[49] = 8'b00010011;
    assign parity_check_matrix[50] = 8'b00010101;
    assign parity_check_matrix[51] = 8'b00010110;
    assign parity_check_matrix[52] = 8'b00000111;
    assign parity_check_matrix[53] = 8'b00001011;
    assign parity_check_matrix[54] = 8'b00001101;
    assign parity_check_matrix[55] = 8'b00001110;
    assign parity_check_matrix[56] = 8'b11111000;
    assign parity_check_matrix[57] = 8'b11100110;
    assign parity_check_matrix[58] = 8'b11011001;
    assign parity_check_matrix[59] = 8'b10110110;
    assign parity_check_matrix[60] = 8'b10001111;
    assign parity_check_matrix[61] = 8'b01111001;
    assign parity_check_matrix[62] = 8'b01100111;
    assign parity_check_matrix[63] = 8'b00011111;
    assign parity_check_matrix[64] = 8'b10000000;
    assign parity_check_matrix[65] = 8'b01000000;
    assign parity_check_matrix[66] = 8'b00100000;
    assign parity_check_matrix[67] = 8'b00010000;
    assign parity_check_matrix[68] = 8'b00001000;
    assign parity_check_matrix[69] = 8'b00000100;
    assign parity_check_matrix[70] = 8'b00000010;
    assign parity_check_matrix[71] = 8'b00000001;
  end else if ((CodewordWidth == 128) && (MessageWidth == 120)) begin : gen_128_120
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 8)
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[120];
    assign syndrome[6] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[112] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[121];
    assign syndrome[5] = cw[0] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[65] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[84] ^ cw[85] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[122];
    assign syndrome[4] = cw[1] ^ cw[6] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[21] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[123];
    assign syndrome[3] = cw[2] ^ cw[7] ^ cw[11] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[22] ^ cw[26] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[36] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[83] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[124];
    assign syndrome[2] = cw[3] ^ cw[8] ^ cw[12] ^ cw[15] ^ cw[19] ^ cw[20] ^ cw[23] ^ cw[27] ^ cw[30] ^ cw[34] ^ cw[35] ^ cw[37] ^ cw[40] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[54] ^ cw[55] ^ cw[57] ^ cw[60] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[118] ^ cw[119] ^ cw[125];
    assign syndrome[1] = cw[4] ^ cw[9] ^ cw[13] ^ cw[16] ^ cw[18] ^ cw[20] ^ cw[24] ^ cw[28] ^ cw[31] ^ cw[33] ^ cw[35] ^ cw[38] ^ cw[41] ^ cw[43] ^ cw[45] ^ cw[47] ^ cw[49] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[55] ^ cw[58] ^ cw[61] ^ cw[63] ^ cw[65] ^ cw[67] ^ cw[69] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[75] ^ cw[77] ^ cw[79] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[90] ^ cw[92] ^ cw[94] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[119] ^ cw[126];
    assign syndrome[0] = cw[5] ^ cw[10] ^ cw[14] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[25] ^ cw[29] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[39] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[59] ^ cw[62] ^ cw[63] ^ cw[64] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[82] ^ cw[83] ^ cw[84] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[127];
    assign parity_check_matrix[0] = 8'b11100000;
    assign parity_check_matrix[1] = 8'b11010000;
    assign parity_check_matrix[2] = 8'b11001000;
    assign parity_check_matrix[3] = 8'b11000100;
    assign parity_check_matrix[4] = 8'b11000010;
    assign parity_check_matrix[5] = 8'b11000001;
    assign parity_check_matrix[6] = 8'b10110000;
    assign parity_check_matrix[7] = 8'b10101000;
    assign parity_check_matrix[8] = 8'b10100100;
    assign parity_check_matrix[9] = 8'b10100010;
    assign parity_check_matrix[10] = 8'b10100001;
    assign parity_check_matrix[11] = 8'b10011000;
    assign parity_check_matrix[12] = 8'b10010100;
    assign parity_check_matrix[13] = 8'b10010010;
    assign parity_check_matrix[14] = 8'b10010001;
    assign parity_check_matrix[15] = 8'b10001100;
    assign parity_check_matrix[16] = 8'b10001010;
    assign parity_check_matrix[17] = 8'b10001001;
    assign parity_check_matrix[18] = 8'b10000011;
    assign parity_check_matrix[19] = 8'b10000101;
    assign parity_check_matrix[20] = 8'b10000110;
    assign parity_check_matrix[21] = 8'b01110000;
    assign parity_check_matrix[22] = 8'b01101000;
    assign parity_check_matrix[23] = 8'b01100100;
    assign parity_check_matrix[24] = 8'b01100010;
    assign parity_check_matrix[25] = 8'b01100001;
    assign parity_check_matrix[26] = 8'b01011000;
    assign parity_check_matrix[27] = 8'b01010100;
    assign parity_check_matrix[28] = 8'b01010010;
    assign parity_check_matrix[29] = 8'b01010001;
    assign parity_check_matrix[30] = 8'b01001100;
    assign parity_check_matrix[31] = 8'b01001010;
    assign parity_check_matrix[32] = 8'b01001001;
    assign parity_check_matrix[33] = 8'b01000011;
    assign parity_check_matrix[34] = 8'b01000101;
    assign parity_check_matrix[35] = 8'b01000110;
    assign parity_check_matrix[36] = 8'b00111000;
    assign parity_check_matrix[37] = 8'b00110100;
    assign parity_check_matrix[38] = 8'b00110010;
    assign parity_check_matrix[39] = 8'b00110001;
    assign parity_check_matrix[40] = 8'b00101100;
    assign parity_check_matrix[41] = 8'b00101010;
    assign parity_check_matrix[42] = 8'b00101001;
    assign parity_check_matrix[43] = 8'b00100011;
    assign parity_check_matrix[44] = 8'b00100101;
    assign parity_check_matrix[45] = 8'b00100110;
    assign parity_check_matrix[46] = 8'b00011100;
    assign parity_check_matrix[47] = 8'b00011010;
    assign parity_check_matrix[48] = 8'b00011001;
    assign parity_check_matrix[49] = 8'b00010011;
    assign parity_check_matrix[50] = 8'b00010101;
    assign parity_check_matrix[51] = 8'b00010110;
    assign parity_check_matrix[52] = 8'b00000111;
    assign parity_check_matrix[53] = 8'b00001011;
    assign parity_check_matrix[54] = 8'b00001101;
    assign parity_check_matrix[55] = 8'b00001110;
    assign parity_check_matrix[56] = 8'b11111000;
    assign parity_check_matrix[57] = 8'b11110100;
    assign parity_check_matrix[58] = 8'b11110010;
    assign parity_check_matrix[59] = 8'b11110001;
    assign parity_check_matrix[60] = 8'b11101100;
    assign parity_check_matrix[61] = 8'b11101010;
    assign parity_check_matrix[62] = 8'b11101001;
    assign parity_check_matrix[63] = 8'b11100011;
    assign parity_check_matrix[64] = 8'b11100101;
    assign parity_check_matrix[65] = 8'b11100110;
    assign parity_check_matrix[66] = 8'b11011100;
    assign parity_check_matrix[67] = 8'b11011010;
    assign parity_check_matrix[68] = 8'b11011001;
    assign parity_check_matrix[69] = 8'b11010011;
    assign parity_check_matrix[70] = 8'b11010101;
    assign parity_check_matrix[71] = 8'b11010110;
    assign parity_check_matrix[72] = 8'b11000111;
    assign parity_check_matrix[73] = 8'b11001011;
    assign parity_check_matrix[74] = 8'b11001101;
    assign parity_check_matrix[75] = 8'b11001110;
    assign parity_check_matrix[76] = 8'b10111100;
    assign parity_check_matrix[77] = 8'b10111010;
    assign parity_check_matrix[78] = 8'b10111001;
    assign parity_check_matrix[79] = 8'b10110011;
    assign parity_check_matrix[80] = 8'b10110101;
    assign parity_check_matrix[81] = 8'b10110110;
    assign parity_check_matrix[82] = 8'b10100111;
    assign parity_check_matrix[83] = 8'b10101011;
    assign parity_check_matrix[84] = 8'b10101101;
    assign parity_check_matrix[85] = 8'b10101110;
    assign parity_check_matrix[86] = 8'b10001111;
    assign parity_check_matrix[87] = 8'b10010111;
    assign parity_check_matrix[88] = 8'b10011011;
    assign parity_check_matrix[89] = 8'b10011101;
    assign parity_check_matrix[90] = 8'b10011110;
    assign parity_check_matrix[91] = 8'b01111100;
    assign parity_check_matrix[92] = 8'b01111010;
    assign parity_check_matrix[93] = 8'b01111001;
    assign parity_check_matrix[94] = 8'b01110011;
    assign parity_check_matrix[95] = 8'b01110101;
    assign parity_check_matrix[96] = 8'b01110110;
    assign parity_check_matrix[97] = 8'b01100111;
    assign parity_check_matrix[98] = 8'b01101011;
    assign parity_check_matrix[99] = 8'b01101101;
    assign parity_check_matrix[100] = 8'b01101110;
    assign parity_check_matrix[101] = 8'b01001111;
    assign parity_check_matrix[102] = 8'b01010111;
    assign parity_check_matrix[103] = 8'b01011011;
    assign parity_check_matrix[104] = 8'b01011101;
    assign parity_check_matrix[105] = 8'b01011110;
    assign parity_check_matrix[106] = 8'b00011111;
    assign parity_check_matrix[107] = 8'b00101111;
    assign parity_check_matrix[108] = 8'b00110111;
    assign parity_check_matrix[109] = 8'b00111011;
    assign parity_check_matrix[110] = 8'b00111101;
    assign parity_check_matrix[111] = 8'b00111110;
    assign parity_check_matrix[112] = 8'b01111111;
    assign parity_check_matrix[113] = 8'b10111111;
    assign parity_check_matrix[114] = 8'b11011111;
    assign parity_check_matrix[115] = 8'b11101111;
    assign parity_check_matrix[116] = 8'b11110111;
    assign parity_check_matrix[117] = 8'b11111011;
    assign parity_check_matrix[118] = 8'b11111101;
    assign parity_check_matrix[119] = 8'b11111110;
    assign parity_check_matrix[120] = 8'b10000000;
    assign parity_check_matrix[121] = 8'b01000000;
    assign parity_check_matrix[122] = 8'b00100000;
    assign parity_check_matrix[123] = 8'b00010000;
    assign parity_check_matrix[124] = 8'b00001000;
    assign parity_check_matrix[125] = 8'b00000100;
    assign parity_check_matrix[126] = 8'b00000010;
    assign parity_check_matrix[127] = 8'b00000001;
  end else if ((CodewordWidth == 137) && (MessageWidth == 128)) begin : gen_137_128
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 9)
    assign syndrome[8] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[128];
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[109] ^ cw[111] ^ cw[114] ^ cw[115] ^ cw[117] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[124] ^ cw[126] ^ cw[127] ^ cw[129];
    assign syndrome[6] = cw[0] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[97] ^ cw[99] ^ cw[102] ^ cw[103] ^ cw[105] ^ cw[107] ^ cw[108] ^ cw[110] ^ cw[111] ^ cw[114] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[121] ^ cw[123] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[130];
    assign syndrome[5] = cw[1] ^ cw[7] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[28] ^ cw[34] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[84] ^ cw[85] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[98] ^ cw[99] ^ cw[102] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[120] ^ cw[122] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[131];
    assign syndrome[4] = cw[2] ^ cw[8] ^ cw[13] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[29] ^ cw[34] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[49] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[84] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[94] ^ cw[96] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[108] ^ cw[112] ^ cw[113] ^ cw[115] ^ cw[118] ^ cw[119] ^ cw[120] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[132];
    assign syndrome[3] = cw[3] ^ cw[9] ^ cw[14] ^ cw[18] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[30] ^ cw[35] ^ cw[39] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[50] ^ cw[54] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[64] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[85] ^ cw[89] ^ cw[90] ^ cw[92] ^ cw[95] ^ cw[96] ^ cw[100] ^ cw[101] ^ cw[103] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[120] ^ cw[133];
    assign syndrome[2] = cw[4] ^ cw[10] ^ cw[15] ^ cw[19] ^ cw[22] ^ cw[26] ^ cw[27] ^ cw[31] ^ cw[36] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[48] ^ cw[51] ^ cw[55] ^ cw[58] ^ cw[62] ^ cw[63] ^ cw[65] ^ cw[68] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[82] ^ cw[83] ^ cw[86] ^ cw[87] ^ cw[91] ^ cw[92] ^ cw[95] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[134];
    assign syndrome[1] = cw[5] ^ cw[11] ^ cw[16] ^ cw[20] ^ cw[23] ^ cw[25] ^ cw[27] ^ cw[32] ^ cw[37] ^ cw[41] ^ cw[44] ^ cw[46] ^ cw[48] ^ cw[52] ^ cw[56] ^ cw[59] ^ cw[61] ^ cw[63] ^ cw[66] ^ cw[69] ^ cw[71] ^ cw[73] ^ cw[75] ^ cw[77] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[83] ^ cw[86] ^ cw[88] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[104] ^ cw[105] ^ cw[107] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[116] ^ cw[117] ^ cw[119] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[127] ^ cw[135];
    assign syndrome[0] = cw[6] ^ cw[12] ^ cw[17] ^ cw[21] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[33] ^ cw[38] ^ cw[42] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[53] ^ cw[57] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[67] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[87] ^ cw[88] ^ cw[93] ^ cw[94] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[101] ^ cw[103] ^ cw[104] ^ cw[106] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[113] ^ cw[115] ^ cw[116] ^ cw[118] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[125] ^ cw[126] ^ cw[136];
    assign parity_check_matrix[0] = 9'b111000000;
    assign parity_check_matrix[1] = 9'b110100000;
    assign parity_check_matrix[2] = 9'b110010000;
    assign parity_check_matrix[3] = 9'b110001000;
    assign parity_check_matrix[4] = 9'b110000100;
    assign parity_check_matrix[5] = 9'b110000010;
    assign parity_check_matrix[6] = 9'b110000001;
    assign parity_check_matrix[7] = 9'b101100000;
    assign parity_check_matrix[8] = 9'b101010000;
    assign parity_check_matrix[9] = 9'b101001000;
    assign parity_check_matrix[10] = 9'b101000100;
    assign parity_check_matrix[11] = 9'b101000010;
    assign parity_check_matrix[12] = 9'b101000001;
    assign parity_check_matrix[13] = 9'b100110000;
    assign parity_check_matrix[14] = 9'b100101000;
    assign parity_check_matrix[15] = 9'b100100100;
    assign parity_check_matrix[16] = 9'b100100010;
    assign parity_check_matrix[17] = 9'b100100001;
    assign parity_check_matrix[18] = 9'b100011000;
    assign parity_check_matrix[19] = 9'b100010100;
    assign parity_check_matrix[20] = 9'b100010010;
    assign parity_check_matrix[21] = 9'b100010001;
    assign parity_check_matrix[22] = 9'b100001100;
    assign parity_check_matrix[23] = 9'b100001010;
    assign parity_check_matrix[24] = 9'b100001001;
    assign parity_check_matrix[25] = 9'b100000011;
    assign parity_check_matrix[26] = 9'b100000101;
    assign parity_check_matrix[27] = 9'b100000110;
    assign parity_check_matrix[28] = 9'b011100000;
    assign parity_check_matrix[29] = 9'b011010000;
    assign parity_check_matrix[30] = 9'b011001000;
    assign parity_check_matrix[31] = 9'b011000100;
    assign parity_check_matrix[32] = 9'b011000010;
    assign parity_check_matrix[33] = 9'b011000001;
    assign parity_check_matrix[34] = 9'b010110000;
    assign parity_check_matrix[35] = 9'b010101000;
    assign parity_check_matrix[36] = 9'b010100100;
    assign parity_check_matrix[37] = 9'b010100010;
    assign parity_check_matrix[38] = 9'b010100001;
    assign parity_check_matrix[39] = 9'b010011000;
    assign parity_check_matrix[40] = 9'b010010100;
    assign parity_check_matrix[41] = 9'b010010010;
    assign parity_check_matrix[42] = 9'b010010001;
    assign parity_check_matrix[43] = 9'b010001100;
    assign parity_check_matrix[44] = 9'b010001010;
    assign parity_check_matrix[45] = 9'b010001001;
    assign parity_check_matrix[46] = 9'b010000011;
    assign parity_check_matrix[47] = 9'b010000101;
    assign parity_check_matrix[48] = 9'b010000110;
    assign parity_check_matrix[49] = 9'b001110000;
    assign parity_check_matrix[50] = 9'b001101000;
    assign parity_check_matrix[51] = 9'b001100100;
    assign parity_check_matrix[52] = 9'b001100010;
    assign parity_check_matrix[53] = 9'b001100001;
    assign parity_check_matrix[54] = 9'b001011000;
    assign parity_check_matrix[55] = 9'b001010100;
    assign parity_check_matrix[56] = 9'b001010010;
    assign parity_check_matrix[57] = 9'b001010001;
    assign parity_check_matrix[58] = 9'b001001100;
    assign parity_check_matrix[59] = 9'b001001010;
    assign parity_check_matrix[60] = 9'b001001001;
    assign parity_check_matrix[61] = 9'b001000011;
    assign parity_check_matrix[62] = 9'b001000101;
    assign parity_check_matrix[63] = 9'b001000110;
    assign parity_check_matrix[64] = 9'b000111000;
    assign parity_check_matrix[65] = 9'b000110100;
    assign parity_check_matrix[66] = 9'b000110010;
    assign parity_check_matrix[67] = 9'b000110001;
    assign parity_check_matrix[68] = 9'b000101100;
    assign parity_check_matrix[69] = 9'b000101010;
    assign parity_check_matrix[70] = 9'b000101001;
    assign parity_check_matrix[71] = 9'b000100011;
    assign parity_check_matrix[72] = 9'b000100101;
    assign parity_check_matrix[73] = 9'b000100110;
    assign parity_check_matrix[74] = 9'b000011100;
    assign parity_check_matrix[75] = 9'b000011010;
    assign parity_check_matrix[76] = 9'b000011001;
    assign parity_check_matrix[77] = 9'b000010011;
    assign parity_check_matrix[78] = 9'b000010101;
    assign parity_check_matrix[79] = 9'b000010110;
    assign parity_check_matrix[80] = 9'b000000111;
    assign parity_check_matrix[81] = 9'b000001011;
    assign parity_check_matrix[82] = 9'b000001101;
    assign parity_check_matrix[83] = 9'b000001110;
    assign parity_check_matrix[84] = 9'b111110000;
    assign parity_check_matrix[85] = 9'b111101000;
    assign parity_check_matrix[86] = 9'b111000110;
    assign parity_check_matrix[87] = 9'b111000101;
    assign parity_check_matrix[88] = 9'b111000011;
    assign parity_check_matrix[89] = 9'b111011000;
    assign parity_check_matrix[90] = 9'b110111000;
    assign parity_check_matrix[91] = 9'b110110100;
    assign parity_check_matrix[92] = 9'b110101100;
    assign parity_check_matrix[93] = 9'b110100011;
    assign parity_check_matrix[94] = 9'b110010011;
    assign parity_check_matrix[95] = 9'b110001110;
    assign parity_check_matrix[96] = 9'b110011001;
    assign parity_check_matrix[97] = 9'b101000111;
    assign parity_check_matrix[98] = 9'b100100111;
    assign parity_check_matrix[99] = 9'b101100110;
    assign parity_check_matrix[100] = 9'b100011110;
    assign parity_check_matrix[101] = 9'b100011101;
    assign parity_check_matrix[102] = 9'b101110100;
    assign parity_check_matrix[103] = 9'b101001101;
    assign parity_check_matrix[104] = 9'b100110011;
    assign parity_check_matrix[105] = 9'b101110010;
    assign parity_check_matrix[106] = 9'b100111001;
    assign parity_check_matrix[107] = 9'b101101010;
    assign parity_check_matrix[108] = 9'b101011001;
    assign parity_check_matrix[109] = 9'b010001111;
    assign parity_check_matrix[110] = 9'b001001111;
    assign parity_check_matrix[111] = 9'b011001110;
    assign parity_check_matrix[112] = 9'b000111110;
    assign parity_check_matrix[113] = 9'b000111101;
    assign parity_check_matrix[114] = 9'b011101100;
    assign parity_check_matrix[115] = 9'b010011101;
    assign parity_check_matrix[116] = 9'b001101011;
    assign parity_check_matrix[117] = 9'b011101010;
    assign parity_check_matrix[118] = 9'b001111001;
    assign parity_check_matrix[119] = 9'b011011010;
    assign parity_check_matrix[120] = 9'b010111001;
    assign parity_check_matrix[121] = 9'b011000111;
    assign parity_check_matrix[122] = 9'b010100111;
    assign parity_check_matrix[123] = 9'b001010111;
    assign parity_check_matrix[124] = 9'b010110110;
    assign parity_check_matrix[125] = 9'b001110101;
    assign parity_check_matrix[126] = 9'b011110001;
    assign parity_check_matrix[127] = 9'b011110010;
    assign parity_check_matrix[128] = 9'b100000000;
    assign parity_check_matrix[129] = 9'b010000000;
    assign parity_check_matrix[130] = 9'b001000000;
    assign parity_check_matrix[131] = 9'b000100000;
    assign parity_check_matrix[132] = 9'b000010000;
    assign parity_check_matrix[133] = 9'b000001000;
    assign parity_check_matrix[134] = 9'b000000100;
    assign parity_check_matrix[135] = 9'b000000010;
    assign parity_check_matrix[136] = 9'b000000001;
  end else if ((CodewordWidth == 256) && (MessageWidth == 247)) begin : gen_256_247
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 9)
    assign syndrome[8] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[246] ^ cw[247];
    assign syndrome[7] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[248];
    assign syndrome[6] = cw[0] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[249];
    assign syndrome[5] = cw[1] ^ cw[7] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[28] ^ cw[34] ^ cw[35] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[84] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[250];
    assign syndrome[4] = cw[2] ^ cw[8] ^ cw[13] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[29] ^ cw[34] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[49] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[84] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[99] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[119] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[251];
    assign syndrome[3] = cw[3] ^ cw[9] ^ cw[14] ^ cw[18] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[30] ^ cw[35] ^ cw[39] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[50] ^ cw[54] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[64] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[85] ^ cw[89] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[99] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[109] ^ cw[110] ^ cw[111] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[252];
    assign syndrome[2] = cw[4] ^ cw[10] ^ cw[15] ^ cw[19] ^ cw[22] ^ cw[26] ^ cw[27] ^ cw[31] ^ cw[36] ^ cw[40] ^ cw[43] ^ cw[47] ^ cw[48] ^ cw[51] ^ cw[55] ^ cw[58] ^ cw[62] ^ cw[63] ^ cw[65] ^ cw[68] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[82] ^ cw[83] ^ cw[86] ^ cw[90] ^ cw[93] ^ cw[97] ^ cw[98] ^ cw[100] ^ cw[103] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[117] ^ cw[118] ^ cw[120] ^ cw[123] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[152] ^ cw[153] ^ cw[155] ^ cw[158] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[253];
    assign syndrome[1] = cw[5] ^ cw[11] ^ cw[16] ^ cw[20] ^ cw[23] ^ cw[25] ^ cw[27] ^ cw[32] ^ cw[37] ^ cw[41] ^ cw[44] ^ cw[46] ^ cw[48] ^ cw[52] ^ cw[56] ^ cw[59] ^ cw[61] ^ cw[63] ^ cw[66] ^ cw[69] ^ cw[71] ^ cw[73] ^ cw[75] ^ cw[77] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[83] ^ cw[87] ^ cw[91] ^ cw[94] ^ cw[96] ^ cw[98] ^ cw[101] ^ cw[104] ^ cw[106] ^ cw[108] ^ cw[110] ^ cw[112] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[118] ^ cw[121] ^ cw[124] ^ cw[126] ^ cw[128] ^ cw[130] ^ cw[132] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[138] ^ cw[140] ^ cw[142] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[153] ^ cw[156] ^ cw[159] ^ cw[161] ^ cw[163] ^ cw[165] ^ cw[167] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[173] ^ cw[175] ^ cw[177] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[188] ^ cw[190] ^ cw[192] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[209] ^ cw[211] ^ cw[213] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[245] ^ cw[246] ^ cw[254];
    assign syndrome[0] = cw[6] ^ cw[12] ^ cw[17] ^ cw[21] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[33] ^ cw[38] ^ cw[42] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[53] ^ cw[57] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[67] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[88] ^ cw[92] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[102] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[122] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[157] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[246] ^ cw[255];
    assign parity_check_matrix[0] = 9'b111000000;
    assign parity_check_matrix[1] = 9'b110100000;
    assign parity_check_matrix[2] = 9'b110010000;
    assign parity_check_matrix[3] = 9'b110001000;
    assign parity_check_matrix[4] = 9'b110000100;
    assign parity_check_matrix[5] = 9'b110000010;
    assign parity_check_matrix[6] = 9'b110000001;
    assign parity_check_matrix[7] = 9'b101100000;
    assign parity_check_matrix[8] = 9'b101010000;
    assign parity_check_matrix[9] = 9'b101001000;
    assign parity_check_matrix[10] = 9'b101000100;
    assign parity_check_matrix[11] = 9'b101000010;
    assign parity_check_matrix[12] = 9'b101000001;
    assign parity_check_matrix[13] = 9'b100110000;
    assign parity_check_matrix[14] = 9'b100101000;
    assign parity_check_matrix[15] = 9'b100100100;
    assign parity_check_matrix[16] = 9'b100100010;
    assign parity_check_matrix[17] = 9'b100100001;
    assign parity_check_matrix[18] = 9'b100011000;
    assign parity_check_matrix[19] = 9'b100010100;
    assign parity_check_matrix[20] = 9'b100010010;
    assign parity_check_matrix[21] = 9'b100010001;
    assign parity_check_matrix[22] = 9'b100001100;
    assign parity_check_matrix[23] = 9'b100001010;
    assign parity_check_matrix[24] = 9'b100001001;
    assign parity_check_matrix[25] = 9'b100000011;
    assign parity_check_matrix[26] = 9'b100000101;
    assign parity_check_matrix[27] = 9'b100000110;
    assign parity_check_matrix[28] = 9'b011100000;
    assign parity_check_matrix[29] = 9'b011010000;
    assign parity_check_matrix[30] = 9'b011001000;
    assign parity_check_matrix[31] = 9'b011000100;
    assign parity_check_matrix[32] = 9'b011000010;
    assign parity_check_matrix[33] = 9'b011000001;
    assign parity_check_matrix[34] = 9'b010110000;
    assign parity_check_matrix[35] = 9'b010101000;
    assign parity_check_matrix[36] = 9'b010100100;
    assign parity_check_matrix[37] = 9'b010100010;
    assign parity_check_matrix[38] = 9'b010100001;
    assign parity_check_matrix[39] = 9'b010011000;
    assign parity_check_matrix[40] = 9'b010010100;
    assign parity_check_matrix[41] = 9'b010010010;
    assign parity_check_matrix[42] = 9'b010010001;
    assign parity_check_matrix[43] = 9'b010001100;
    assign parity_check_matrix[44] = 9'b010001010;
    assign parity_check_matrix[45] = 9'b010001001;
    assign parity_check_matrix[46] = 9'b010000011;
    assign parity_check_matrix[47] = 9'b010000101;
    assign parity_check_matrix[48] = 9'b010000110;
    assign parity_check_matrix[49] = 9'b001110000;
    assign parity_check_matrix[50] = 9'b001101000;
    assign parity_check_matrix[51] = 9'b001100100;
    assign parity_check_matrix[52] = 9'b001100010;
    assign parity_check_matrix[53] = 9'b001100001;
    assign parity_check_matrix[54] = 9'b001011000;
    assign parity_check_matrix[55] = 9'b001010100;
    assign parity_check_matrix[56] = 9'b001010010;
    assign parity_check_matrix[57] = 9'b001010001;
    assign parity_check_matrix[58] = 9'b001001100;
    assign parity_check_matrix[59] = 9'b001001010;
    assign parity_check_matrix[60] = 9'b001001001;
    assign parity_check_matrix[61] = 9'b001000011;
    assign parity_check_matrix[62] = 9'b001000101;
    assign parity_check_matrix[63] = 9'b001000110;
    assign parity_check_matrix[64] = 9'b000111000;
    assign parity_check_matrix[65] = 9'b000110100;
    assign parity_check_matrix[66] = 9'b000110010;
    assign parity_check_matrix[67] = 9'b000110001;
    assign parity_check_matrix[68] = 9'b000101100;
    assign parity_check_matrix[69] = 9'b000101010;
    assign parity_check_matrix[70] = 9'b000101001;
    assign parity_check_matrix[71] = 9'b000100011;
    assign parity_check_matrix[72] = 9'b000100101;
    assign parity_check_matrix[73] = 9'b000100110;
    assign parity_check_matrix[74] = 9'b000011100;
    assign parity_check_matrix[75] = 9'b000011010;
    assign parity_check_matrix[76] = 9'b000011001;
    assign parity_check_matrix[77] = 9'b000010011;
    assign parity_check_matrix[78] = 9'b000010101;
    assign parity_check_matrix[79] = 9'b000010110;
    assign parity_check_matrix[80] = 9'b000000111;
    assign parity_check_matrix[81] = 9'b000001011;
    assign parity_check_matrix[82] = 9'b000001101;
    assign parity_check_matrix[83] = 9'b000001110;
    assign parity_check_matrix[84] = 9'b111110000;
    assign parity_check_matrix[85] = 9'b111101000;
    assign parity_check_matrix[86] = 9'b111100100;
    assign parity_check_matrix[87] = 9'b111100010;
    assign parity_check_matrix[88] = 9'b111100001;
    assign parity_check_matrix[89] = 9'b111011000;
    assign parity_check_matrix[90] = 9'b111010100;
    assign parity_check_matrix[91] = 9'b111010010;
    assign parity_check_matrix[92] = 9'b111010001;
    assign parity_check_matrix[93] = 9'b111001100;
    assign parity_check_matrix[94] = 9'b111001010;
    assign parity_check_matrix[95] = 9'b111001001;
    assign parity_check_matrix[96] = 9'b111000011;
    assign parity_check_matrix[97] = 9'b111000101;
    assign parity_check_matrix[98] = 9'b111000110;
    assign parity_check_matrix[99] = 9'b110111000;
    assign parity_check_matrix[100] = 9'b110110100;
    assign parity_check_matrix[101] = 9'b110110010;
    assign parity_check_matrix[102] = 9'b110110001;
    assign parity_check_matrix[103] = 9'b110101100;
    assign parity_check_matrix[104] = 9'b110101010;
    assign parity_check_matrix[105] = 9'b110101001;
    assign parity_check_matrix[106] = 9'b110100011;
    assign parity_check_matrix[107] = 9'b110100101;
    assign parity_check_matrix[108] = 9'b110100110;
    assign parity_check_matrix[109] = 9'b110011100;
    assign parity_check_matrix[110] = 9'b110011010;
    assign parity_check_matrix[111] = 9'b110011001;
    assign parity_check_matrix[112] = 9'b110010011;
    assign parity_check_matrix[113] = 9'b110010101;
    assign parity_check_matrix[114] = 9'b110010110;
    assign parity_check_matrix[115] = 9'b110000111;
    assign parity_check_matrix[116] = 9'b110001011;
    assign parity_check_matrix[117] = 9'b110001101;
    assign parity_check_matrix[118] = 9'b110001110;
    assign parity_check_matrix[119] = 9'b101111000;
    assign parity_check_matrix[120] = 9'b101110100;
    assign parity_check_matrix[121] = 9'b101110010;
    assign parity_check_matrix[122] = 9'b101110001;
    assign parity_check_matrix[123] = 9'b101101100;
    assign parity_check_matrix[124] = 9'b101101010;
    assign parity_check_matrix[125] = 9'b101101001;
    assign parity_check_matrix[126] = 9'b101100011;
    assign parity_check_matrix[127] = 9'b101100101;
    assign parity_check_matrix[128] = 9'b101100110;
    assign parity_check_matrix[129] = 9'b101011100;
    assign parity_check_matrix[130] = 9'b101011010;
    assign parity_check_matrix[131] = 9'b101011001;
    assign parity_check_matrix[132] = 9'b101010011;
    assign parity_check_matrix[133] = 9'b101010101;
    assign parity_check_matrix[134] = 9'b101010110;
    assign parity_check_matrix[135] = 9'b101000111;
    assign parity_check_matrix[136] = 9'b101001011;
    assign parity_check_matrix[137] = 9'b101001101;
    assign parity_check_matrix[138] = 9'b101001110;
    assign parity_check_matrix[139] = 9'b100111100;
    assign parity_check_matrix[140] = 9'b100111010;
    assign parity_check_matrix[141] = 9'b100111001;
    assign parity_check_matrix[142] = 9'b100110011;
    assign parity_check_matrix[143] = 9'b100110101;
    assign parity_check_matrix[144] = 9'b100110110;
    assign parity_check_matrix[145] = 9'b100100111;
    assign parity_check_matrix[146] = 9'b100101011;
    assign parity_check_matrix[147] = 9'b100101101;
    assign parity_check_matrix[148] = 9'b100101110;
    assign parity_check_matrix[149] = 9'b100001111;
    assign parity_check_matrix[150] = 9'b100010111;
    assign parity_check_matrix[151] = 9'b100011011;
    assign parity_check_matrix[152] = 9'b100011101;
    assign parity_check_matrix[153] = 9'b100011110;
    assign parity_check_matrix[154] = 9'b011111000;
    assign parity_check_matrix[155] = 9'b011110100;
    assign parity_check_matrix[156] = 9'b011110010;
    assign parity_check_matrix[157] = 9'b011110001;
    assign parity_check_matrix[158] = 9'b011101100;
    assign parity_check_matrix[159] = 9'b011101010;
    assign parity_check_matrix[160] = 9'b011101001;
    assign parity_check_matrix[161] = 9'b011100011;
    assign parity_check_matrix[162] = 9'b011100101;
    assign parity_check_matrix[163] = 9'b011100110;
    assign parity_check_matrix[164] = 9'b011011100;
    assign parity_check_matrix[165] = 9'b011011010;
    assign parity_check_matrix[166] = 9'b011011001;
    assign parity_check_matrix[167] = 9'b011010011;
    assign parity_check_matrix[168] = 9'b011010101;
    assign parity_check_matrix[169] = 9'b011010110;
    assign parity_check_matrix[170] = 9'b011000111;
    assign parity_check_matrix[171] = 9'b011001011;
    assign parity_check_matrix[172] = 9'b011001101;
    assign parity_check_matrix[173] = 9'b011001110;
    assign parity_check_matrix[174] = 9'b010111100;
    assign parity_check_matrix[175] = 9'b010111010;
    assign parity_check_matrix[176] = 9'b010111001;
    assign parity_check_matrix[177] = 9'b010110011;
    assign parity_check_matrix[178] = 9'b010110101;
    assign parity_check_matrix[179] = 9'b010110110;
    assign parity_check_matrix[180] = 9'b010100111;
    assign parity_check_matrix[181] = 9'b010101011;
    assign parity_check_matrix[182] = 9'b010101101;
    assign parity_check_matrix[183] = 9'b010101110;
    assign parity_check_matrix[184] = 9'b010001111;
    assign parity_check_matrix[185] = 9'b010010111;
    assign parity_check_matrix[186] = 9'b010011011;
    assign parity_check_matrix[187] = 9'b010011101;
    assign parity_check_matrix[188] = 9'b010011110;
    assign parity_check_matrix[189] = 9'b001111100;
    assign parity_check_matrix[190] = 9'b001111010;
    assign parity_check_matrix[191] = 9'b001111001;
    assign parity_check_matrix[192] = 9'b001110011;
    assign parity_check_matrix[193] = 9'b001110101;
    assign parity_check_matrix[194] = 9'b001110110;
    assign parity_check_matrix[195] = 9'b001100111;
    assign parity_check_matrix[196] = 9'b001101011;
    assign parity_check_matrix[197] = 9'b001101101;
    assign parity_check_matrix[198] = 9'b001101110;
    assign parity_check_matrix[199] = 9'b001001111;
    assign parity_check_matrix[200] = 9'b001010111;
    assign parity_check_matrix[201] = 9'b001011011;
    assign parity_check_matrix[202] = 9'b001011101;
    assign parity_check_matrix[203] = 9'b001011110;
    assign parity_check_matrix[204] = 9'b000011111;
    assign parity_check_matrix[205] = 9'b000101111;
    assign parity_check_matrix[206] = 9'b000110111;
    assign parity_check_matrix[207] = 9'b000111011;
    assign parity_check_matrix[208] = 9'b000111101;
    assign parity_check_matrix[209] = 9'b000111110;
    assign parity_check_matrix[210] = 9'b111111100;
    assign parity_check_matrix[211] = 9'b111111010;
    assign parity_check_matrix[212] = 9'b111111001;
    assign parity_check_matrix[213] = 9'b111110011;
    assign parity_check_matrix[214] = 9'b111110101;
    assign parity_check_matrix[215] = 9'b111110110;
    assign parity_check_matrix[216] = 9'b111100111;
    assign parity_check_matrix[217] = 9'b111101011;
    assign parity_check_matrix[218] = 9'b111101101;
    assign parity_check_matrix[219] = 9'b111101110;
    assign parity_check_matrix[220] = 9'b111001111;
    assign parity_check_matrix[221] = 9'b111010111;
    assign parity_check_matrix[222] = 9'b111011011;
    assign parity_check_matrix[223] = 9'b111011101;
    assign parity_check_matrix[224] = 9'b111011110;
    assign parity_check_matrix[225] = 9'b110011111;
    assign parity_check_matrix[226] = 9'b110101111;
    assign parity_check_matrix[227] = 9'b110110111;
    assign parity_check_matrix[228] = 9'b110111011;
    assign parity_check_matrix[229] = 9'b110111101;
    assign parity_check_matrix[230] = 9'b110111110;
    assign parity_check_matrix[231] = 9'b100111111;
    assign parity_check_matrix[232] = 9'b101011111;
    assign parity_check_matrix[233] = 9'b101101111;
    assign parity_check_matrix[234] = 9'b101110111;
    assign parity_check_matrix[235] = 9'b101111011;
    assign parity_check_matrix[236] = 9'b101111101;
    assign parity_check_matrix[237] = 9'b101111110;
    assign parity_check_matrix[238] = 9'b001111111;
    assign parity_check_matrix[239] = 9'b010111111;
    assign parity_check_matrix[240] = 9'b011011111;
    assign parity_check_matrix[241] = 9'b011101111;
    assign parity_check_matrix[242] = 9'b011110111;
    assign parity_check_matrix[243] = 9'b011111011;
    assign parity_check_matrix[244] = 9'b011111101;
    assign parity_check_matrix[245] = 9'b011111110;
    assign parity_check_matrix[246] = 9'b111111111;
    assign parity_check_matrix[247] = 9'b100000000;
    assign parity_check_matrix[248] = 9'b010000000;
    assign parity_check_matrix[249] = 9'b001000000;
    assign parity_check_matrix[250] = 9'b000100000;
    assign parity_check_matrix[251] = 9'b000010000;
    assign parity_check_matrix[252] = 9'b000001000;
    assign parity_check_matrix[253] = 9'b000000100;
    assign parity_check_matrix[254] = 9'b000000010;
    assign parity_check_matrix[255] = 9'b000000001;
  end else if ((CodewordWidth == 266) && (MessageWidth == 256)) begin : gen_266_256
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 10)
    assign syndrome[9] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[35] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[256];
    assign syndrome[8] = cw[0] ^ cw[1] ^ cw[2] ^ cw[3] ^ cw[4] ^ cw[5] ^ cw[6] ^ cw[7] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[63] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[199] ^ cw[200] ^ cw[203] ^ cw[205] ^ cw[206] ^ cw[208] ^ cw[211] ^ cw[213] ^ cw[215] ^ cw[216] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[228] ^ cw[231] ^ cw[233] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[243] ^ cw[244] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[257];
    assign syndrome[7] = cw[0] ^ cw[8] ^ cw[9] ^ cw[10] ^ cw[11] ^ cw[12] ^ cw[13] ^ cw[14] ^ cw[36] ^ cw[37] ^ cw[38] ^ cw[39] ^ cw[40] ^ cw[41] ^ cw[42] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[84] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[127] ^ cw[128] ^ cw[129] ^ cw[130] ^ cw[131] ^ cw[151] ^ cw[155] ^ cw[158] ^ cw[160] ^ cw[161] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[181] ^ cw[183] ^ cw[184] ^ cw[186] ^ cw[187] ^ cw[191] ^ cw[194] ^ cw[196] ^ cw[199] ^ cw[201] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[209] ^ cw[212] ^ cw[214] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[224] ^ cw[225] ^ cw[229] ^ cw[230] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[258];
    assign syndrome[6] = cw[1] ^ cw[8] ^ cw[15] ^ cw[16] ^ cw[17] ^ cw[18] ^ cw[19] ^ cw[20] ^ cw[36] ^ cw[43] ^ cw[44] ^ cw[45] ^ cw[46] ^ cw[47] ^ cw[48] ^ cw[64] ^ cw[65] ^ cw[66] ^ cw[67] ^ cw[68] ^ cw[69] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[99] ^ cw[120] ^ cw[121] ^ cw[122] ^ cw[123] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[141] ^ cw[142] ^ cw[143] ^ cw[144] ^ cw[145] ^ cw[152] ^ cw[156] ^ cw[159] ^ cw[160] ^ cw[163] ^ cw[165] ^ cw[166] ^ cw[169] ^ cw[170] ^ cw[173] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[180] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[186] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[218] ^ cw[219] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[259];
    assign syndrome[5] = cw[2] ^ cw[9] ^ cw[15] ^ cw[21] ^ cw[22] ^ cw[23] ^ cw[24] ^ cw[25] ^ cw[37] ^ cw[43] ^ cw[49] ^ cw[50] ^ cw[51] ^ cw[52] ^ cw[53] ^ cw[64] ^ cw[70] ^ cw[71] ^ cw[72] ^ cw[73] ^ cw[74] ^ cw[85] ^ cw[86] ^ cw[87] ^ cw[88] ^ cw[89] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[109] ^ cw[120] ^ cw[125] ^ cw[127] ^ cw[130] ^ cw[132] ^ cw[136] ^ cw[139] ^ cw[141] ^ cw[142] ^ cw[146] ^ cw[147] ^ cw[148] ^ cw[153] ^ cw[157] ^ cw[158] ^ cw[161] ^ cw[164] ^ cw[165] ^ cw[167] ^ cw[168] ^ cw[171] ^ cw[174] ^ cw[176] ^ cw[178] ^ cw[179] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[184] ^ cw[185] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[205] ^ cw[206] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[260];
    assign syndrome[4] = cw[3] ^ cw[10] ^ cw[16] ^ cw[21] ^ cw[26] ^ cw[27] ^ cw[28] ^ cw[29] ^ cw[38] ^ cw[44] ^ cw[49] ^ cw[54] ^ cw[55] ^ cw[56] ^ cw[57] ^ cw[65] ^ cw[70] ^ cw[75] ^ cw[76] ^ cw[77] ^ cw[78] ^ cw[85] ^ cw[90] ^ cw[91] ^ cw[92] ^ cw[93] ^ cw[100] ^ cw[101] ^ cw[102] ^ cw[103] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[115] ^ cw[121] ^ cw[126] ^ cw[128] ^ cw[131] ^ cw[133] ^ cw[137] ^ cw[140] ^ cw[141] ^ cw[144] ^ cw[146] ^ cw[147] ^ cw[150] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[162] ^ cw[163] ^ cw[166] ^ cw[168] ^ cw[169] ^ cw[172] ^ cw[175] ^ cw[177] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[183] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[191] ^ cw[192] ^ cw[193] ^ cw[194] ^ cw[195] ^ cw[196] ^ cw[210] ^ cw[211] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[220] ^ cw[221] ^ cw[222] ^ cw[224] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[235] ^ cw[236] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[254] ^ cw[255] ^ cw[261];
    assign syndrome[3] = cw[4] ^ cw[11] ^ cw[17] ^ cw[22] ^ cw[26] ^ cw[30] ^ cw[31] ^ cw[32] ^ cw[39] ^ cw[45] ^ cw[50] ^ cw[54] ^ cw[58] ^ cw[59] ^ cw[60] ^ cw[66] ^ cw[71] ^ cw[75] ^ cw[79] ^ cw[80] ^ cw[81] ^ cw[86] ^ cw[90] ^ cw[94] ^ cw[95] ^ cw[96] ^ cw[100] ^ cw[104] ^ cw[105] ^ cw[106] ^ cw[110] ^ cw[111] ^ cw[112] ^ cw[117] ^ cw[118] ^ cw[119] ^ cw[122] ^ cw[129] ^ cw[130] ^ cw[132] ^ cw[133] ^ cw[134] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[138] ^ cw[139] ^ cw[140] ^ cw[154] ^ cw[157] ^ cw[159] ^ cw[162] ^ cw[164] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[173] ^ cw[174] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[181] ^ cw[182] ^ cw[185] ^ cw[186] ^ cw[187] ^ cw[188] ^ cw[189] ^ cw[190] ^ cw[197] ^ cw[198] ^ cw[199] ^ cw[200] ^ cw[201] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[216] ^ cw[217] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[229] ^ cw[230] ^ cw[231] ^ cw[237] ^ cw[238] ^ cw[241] ^ cw[242] ^ cw[244] ^ cw[245] ^ cw[246] ^ cw[247] ^ cw[248] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[255] ^ cw[262];
    assign syndrome[2] = cw[5] ^ cw[12] ^ cw[18] ^ cw[23] ^ cw[27] ^ cw[30] ^ cw[34] ^ cw[35] ^ cw[40] ^ cw[46] ^ cw[51] ^ cw[55] ^ cw[58] ^ cw[62] ^ cw[63] ^ cw[67] ^ cw[72] ^ cw[76] ^ cw[79] ^ cw[83] ^ cw[84] ^ cw[87] ^ cw[91] ^ cw[94] ^ cw[98] ^ cw[99] ^ cw[101] ^ cw[104] ^ cw[108] ^ cw[109] ^ cw[110] ^ cw[114] ^ cw[115] ^ cw[116] ^ cw[118] ^ cw[119] ^ cw[123] ^ cw[129] ^ cw[131] ^ cw[134] ^ cw[138] ^ cw[139] ^ cw[142] ^ cw[145] ^ cw[146] ^ cw[148] ^ cw[149] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[165] ^ cw[166] ^ cw[167] ^ cw[168] ^ cw[169] ^ cw[188] ^ cw[192] ^ cw[195] ^ cw[197] ^ cw[198] ^ cw[202] ^ cw[203] ^ cw[204] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[210] ^ cw[211] ^ cw[212] ^ cw[218] ^ cw[219] ^ cw[222] ^ cw[223] ^ cw[225] ^ cw[226] ^ cw[227] ^ cw[228] ^ cw[232] ^ cw[233] ^ cw[234] ^ cw[237] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[243] ^ cw[245] ^ cw[246] ^ cw[249] ^ cw[250] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[263];
    assign syndrome[1] = cw[6] ^ cw[13] ^ cw[19] ^ cw[24] ^ cw[28] ^ cw[31] ^ cw[33] ^ cw[35] ^ cw[41] ^ cw[47] ^ cw[52] ^ cw[56] ^ cw[59] ^ cw[61] ^ cw[63] ^ cw[68] ^ cw[73] ^ cw[77] ^ cw[80] ^ cw[82] ^ cw[84] ^ cw[88] ^ cw[92] ^ cw[95] ^ cw[97] ^ cw[99] ^ cw[102] ^ cw[105] ^ cw[107] ^ cw[109] ^ cw[111] ^ cw[113] ^ cw[115] ^ cw[116] ^ cw[117] ^ cw[119] ^ cw[124] ^ cw[125] ^ cw[126] ^ cw[135] ^ cw[136] ^ cw[137] ^ cw[143] ^ cw[144] ^ cw[147] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[154] ^ cw[155] ^ cw[156] ^ cw[157] ^ cw[158] ^ cw[159] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[182] ^ cw[184] ^ cw[185] ^ cw[187] ^ cw[189] ^ cw[193] ^ cw[196] ^ cw[197] ^ cw[200] ^ cw[202] ^ cw[203] ^ cw[206] ^ cw[207] ^ cw[208] ^ cw[209] ^ cw[213] ^ cw[214] ^ cw[215] ^ cw[218] ^ cw[221] ^ cw[222] ^ cw[223] ^ cw[224] ^ cw[226] ^ cw[229] ^ cw[231] ^ cw[232] ^ cw[233] ^ cw[236] ^ cw[238] ^ cw[239] ^ cw[242] ^ cw[243] ^ cw[244] ^ cw[245] ^ cw[248] ^ cw[249] ^ cw[250] ^ cw[251] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[264];
    assign syndrome[0] = cw[7] ^ cw[14] ^ cw[20] ^ cw[25] ^ cw[29] ^ cw[32] ^ cw[33] ^ cw[34] ^ cw[42] ^ cw[48] ^ cw[53] ^ cw[57] ^ cw[60] ^ cw[61] ^ cw[62] ^ cw[69] ^ cw[74] ^ cw[78] ^ cw[81] ^ cw[82] ^ cw[83] ^ cw[89] ^ cw[93] ^ cw[96] ^ cw[97] ^ cw[98] ^ cw[103] ^ cw[106] ^ cw[107] ^ cw[108] ^ cw[112] ^ cw[113] ^ cw[114] ^ cw[116] ^ cw[117] ^ cw[118] ^ cw[124] ^ cw[127] ^ cw[128] ^ cw[135] ^ cw[138] ^ cw[140] ^ cw[143] ^ cw[145] ^ cw[148] ^ cw[149] ^ cw[150] ^ cw[151] ^ cw[152] ^ cw[153] ^ cw[160] ^ cw[161] ^ cw[162] ^ cw[163] ^ cw[164] ^ cw[170] ^ cw[171] ^ cw[172] ^ cw[173] ^ cw[174] ^ cw[175] ^ cw[176] ^ cw[177] ^ cw[178] ^ cw[179] ^ cw[180] ^ cw[190] ^ cw[194] ^ cw[195] ^ cw[198] ^ cw[201] ^ cw[202] ^ cw[204] ^ cw[205] ^ cw[207] ^ cw[210] ^ cw[212] ^ cw[213] ^ cw[214] ^ cw[217] ^ cw[219] ^ cw[220] ^ cw[223] ^ cw[224] ^ cw[225] ^ cw[227] ^ cw[230] ^ cw[232] ^ cw[234] ^ cw[235] ^ cw[237] ^ cw[238] ^ cw[239] ^ cw[240] ^ cw[241] ^ cw[242] ^ cw[246] ^ cw[247] ^ cw[250] ^ cw[251] ^ cw[252] ^ cw[253] ^ cw[254] ^ cw[255] ^ cw[265];
    assign parity_check_matrix[0] = 10'b1110000000;
    assign parity_check_matrix[1] = 10'b1101000000;
    assign parity_check_matrix[2] = 10'b1100100000;
    assign parity_check_matrix[3] = 10'b1100010000;
    assign parity_check_matrix[4] = 10'b1100001000;
    assign parity_check_matrix[5] = 10'b1100000100;
    assign parity_check_matrix[6] = 10'b1100000010;
    assign parity_check_matrix[7] = 10'b1100000001;
    assign parity_check_matrix[8] = 10'b1011000000;
    assign parity_check_matrix[9] = 10'b1010100000;
    assign parity_check_matrix[10] = 10'b1010010000;
    assign parity_check_matrix[11] = 10'b1010001000;
    assign parity_check_matrix[12] = 10'b1010000100;
    assign parity_check_matrix[13] = 10'b1010000010;
    assign parity_check_matrix[14] = 10'b1010000001;
    assign parity_check_matrix[15] = 10'b1001100000;
    assign parity_check_matrix[16] = 10'b1001010000;
    assign parity_check_matrix[17] = 10'b1001001000;
    assign parity_check_matrix[18] = 10'b1001000100;
    assign parity_check_matrix[19] = 10'b1001000010;
    assign parity_check_matrix[20] = 10'b1001000001;
    assign parity_check_matrix[21] = 10'b1000110000;
    assign parity_check_matrix[22] = 10'b1000101000;
    assign parity_check_matrix[23] = 10'b1000100100;
    assign parity_check_matrix[24] = 10'b1000100010;
    assign parity_check_matrix[25] = 10'b1000100001;
    assign parity_check_matrix[26] = 10'b1000011000;
    assign parity_check_matrix[27] = 10'b1000010100;
    assign parity_check_matrix[28] = 10'b1000010010;
    assign parity_check_matrix[29] = 10'b1000010001;
    assign parity_check_matrix[30] = 10'b1000001100;
    assign parity_check_matrix[31] = 10'b1000001010;
    assign parity_check_matrix[32] = 10'b1000001001;
    assign parity_check_matrix[33] = 10'b1000000011;
    assign parity_check_matrix[34] = 10'b1000000101;
    assign parity_check_matrix[35] = 10'b1000000110;
    assign parity_check_matrix[36] = 10'b0111000000;
    assign parity_check_matrix[37] = 10'b0110100000;
    assign parity_check_matrix[38] = 10'b0110010000;
    assign parity_check_matrix[39] = 10'b0110001000;
    assign parity_check_matrix[40] = 10'b0110000100;
    assign parity_check_matrix[41] = 10'b0110000010;
    assign parity_check_matrix[42] = 10'b0110000001;
    assign parity_check_matrix[43] = 10'b0101100000;
    assign parity_check_matrix[44] = 10'b0101010000;
    assign parity_check_matrix[45] = 10'b0101001000;
    assign parity_check_matrix[46] = 10'b0101000100;
    assign parity_check_matrix[47] = 10'b0101000010;
    assign parity_check_matrix[48] = 10'b0101000001;
    assign parity_check_matrix[49] = 10'b0100110000;
    assign parity_check_matrix[50] = 10'b0100101000;
    assign parity_check_matrix[51] = 10'b0100100100;
    assign parity_check_matrix[52] = 10'b0100100010;
    assign parity_check_matrix[53] = 10'b0100100001;
    assign parity_check_matrix[54] = 10'b0100011000;
    assign parity_check_matrix[55] = 10'b0100010100;
    assign parity_check_matrix[56] = 10'b0100010010;
    assign parity_check_matrix[57] = 10'b0100010001;
    assign parity_check_matrix[58] = 10'b0100001100;
    assign parity_check_matrix[59] = 10'b0100001010;
    assign parity_check_matrix[60] = 10'b0100001001;
    assign parity_check_matrix[61] = 10'b0100000011;
    assign parity_check_matrix[62] = 10'b0100000101;
    assign parity_check_matrix[63] = 10'b0100000110;
    assign parity_check_matrix[64] = 10'b0011100000;
    assign parity_check_matrix[65] = 10'b0011010000;
    assign parity_check_matrix[66] = 10'b0011001000;
    assign parity_check_matrix[67] = 10'b0011000100;
    assign parity_check_matrix[68] = 10'b0011000010;
    assign parity_check_matrix[69] = 10'b0011000001;
    assign parity_check_matrix[70] = 10'b0010110000;
    assign parity_check_matrix[71] = 10'b0010101000;
    assign parity_check_matrix[72] = 10'b0010100100;
    assign parity_check_matrix[73] = 10'b0010100010;
    assign parity_check_matrix[74] = 10'b0010100001;
    assign parity_check_matrix[75] = 10'b0010011000;
    assign parity_check_matrix[76] = 10'b0010010100;
    assign parity_check_matrix[77] = 10'b0010010010;
    assign parity_check_matrix[78] = 10'b0010010001;
    assign parity_check_matrix[79] = 10'b0010001100;
    assign parity_check_matrix[80] = 10'b0010001010;
    assign parity_check_matrix[81] = 10'b0010001001;
    assign parity_check_matrix[82] = 10'b0010000011;
    assign parity_check_matrix[83] = 10'b0010000101;
    assign parity_check_matrix[84] = 10'b0010000110;
    assign parity_check_matrix[85] = 10'b0001110000;
    assign parity_check_matrix[86] = 10'b0001101000;
    assign parity_check_matrix[87] = 10'b0001100100;
    assign parity_check_matrix[88] = 10'b0001100010;
    assign parity_check_matrix[89] = 10'b0001100001;
    assign parity_check_matrix[90] = 10'b0001011000;
    assign parity_check_matrix[91] = 10'b0001010100;
    assign parity_check_matrix[92] = 10'b0001010010;
    assign parity_check_matrix[93] = 10'b0001010001;
    assign parity_check_matrix[94] = 10'b0001001100;
    assign parity_check_matrix[95] = 10'b0001001010;
    assign parity_check_matrix[96] = 10'b0001001001;
    assign parity_check_matrix[97] = 10'b0001000011;
    assign parity_check_matrix[98] = 10'b0001000101;
    assign parity_check_matrix[99] = 10'b0001000110;
    assign parity_check_matrix[100] = 10'b0000111000;
    assign parity_check_matrix[101] = 10'b0000110100;
    assign parity_check_matrix[102] = 10'b0000110010;
    assign parity_check_matrix[103] = 10'b0000110001;
    assign parity_check_matrix[104] = 10'b0000101100;
    assign parity_check_matrix[105] = 10'b0000101010;
    assign parity_check_matrix[106] = 10'b0000101001;
    assign parity_check_matrix[107] = 10'b0000100011;
    assign parity_check_matrix[108] = 10'b0000100101;
    assign parity_check_matrix[109] = 10'b0000100110;
    assign parity_check_matrix[110] = 10'b0000011100;
    assign parity_check_matrix[111] = 10'b0000011010;
    assign parity_check_matrix[112] = 10'b0000011001;
    assign parity_check_matrix[113] = 10'b0000010011;
    assign parity_check_matrix[114] = 10'b0000010101;
    assign parity_check_matrix[115] = 10'b0000010110;
    assign parity_check_matrix[116] = 10'b0000000111;
    assign parity_check_matrix[117] = 10'b0000001011;
    assign parity_check_matrix[118] = 10'b0000001101;
    assign parity_check_matrix[119] = 10'b0000001110;
    assign parity_check_matrix[120] = 10'b1111100000;
    assign parity_check_matrix[121] = 10'b1111010000;
    assign parity_check_matrix[122] = 10'b1111001000;
    assign parity_check_matrix[123] = 10'b1111000100;
    assign parity_check_matrix[124] = 10'b1110000011;
    assign parity_check_matrix[125] = 10'b1110100010;
    assign parity_check_matrix[126] = 10'b1110010010;
    assign parity_check_matrix[127] = 10'b1110100001;
    assign parity_check_matrix[128] = 10'b1110010001;
    assign parity_check_matrix[129] = 10'b1110001100;
    assign parity_check_matrix[130] = 10'b1110101000;
    assign parity_check_matrix[131] = 10'b1110010100;
    assign parity_check_matrix[132] = 10'b1101101000;
    assign parity_check_matrix[133] = 10'b1101011000;
    assign parity_check_matrix[134] = 10'b1101001100;
    assign parity_check_matrix[135] = 10'b1100001011;
    assign parity_check_matrix[136] = 10'b1100101010;
    assign parity_check_matrix[137] = 10'b1100011010;
    assign parity_check_matrix[138] = 10'b1100001101;
    assign parity_check_matrix[139] = 10'b1100101100;
    assign parity_check_matrix[140] = 10'b1100011001;
    assign parity_check_matrix[141] = 10'b1101110000;
    assign parity_check_matrix[142] = 10'b1101100100;
    assign parity_check_matrix[143] = 10'b1101000011;
    assign parity_check_matrix[144] = 10'b1101010010;
    assign parity_check_matrix[145] = 10'b1101000101;
    assign parity_check_matrix[146] = 10'b1100110100;
    assign parity_check_matrix[147] = 10'b1100110010;
    assign parity_check_matrix[148] = 10'b1100100101;
    assign parity_check_matrix[149] = 10'b1100000111;
    assign parity_check_matrix[150] = 10'b1100010011;
    assign parity_check_matrix[151] = 10'b1010000111;
    assign parity_check_matrix[152] = 10'b1001000111;
    assign parity_check_matrix[153] = 10'b1000100111;
    assign parity_check_matrix[154] = 10'b1000011110;
    assign parity_check_matrix[155] = 10'b1010010110;
    assign parity_check_matrix[156] = 10'b1001010110;
    assign parity_check_matrix[157] = 10'b1000101110;
    assign parity_check_matrix[158] = 10'b1010100110;
    assign parity_check_matrix[159] = 10'b1001001110;
    assign parity_check_matrix[160] = 10'b1011000101;
    assign parity_check_matrix[161] = 10'b1010100101;
    assign parity_check_matrix[162] = 10'b1000011101;
    assign parity_check_matrix[163] = 10'b1001010101;
    assign parity_check_matrix[164] = 10'b1000101101;
    assign parity_check_matrix[165] = 10'b1011100100;
    assign parity_check_matrix[166] = 10'b1011010100;
    assign parity_check_matrix[167] = 10'b1010101100;
    assign parity_check_matrix[168] = 10'b1000111100;
    assign parity_check_matrix[169] = 10'b1001011100;
    assign parity_check_matrix[170] = 10'b1011000011;
    assign parity_check_matrix[171] = 10'b1010100011;
    assign parity_check_matrix[172] = 10'b1010010011;
    assign parity_check_matrix[173] = 10'b1011001001;
    assign parity_check_matrix[174] = 10'b1010101001;
    assign parity_check_matrix[175] = 10'b1011010001;
    assign parity_check_matrix[176] = 10'b1001100011;
    assign parity_check_matrix[177] = 10'b1001010011;
    assign parity_check_matrix[178] = 10'b1000101011;
    assign parity_check_matrix[179] = 10'b1000111001;
    assign parity_check_matrix[180] = 10'b1001011001;
    assign parity_check_matrix[181] = 10'b1010111000;
    assign parity_check_matrix[182] = 10'b1000111010;
    assign parity_check_matrix[183] = 10'b1011110000;
    assign parity_check_matrix[184] = 10'b1011100010;
    assign parity_check_matrix[185] = 10'b1001101010;
    assign parity_check_matrix[186] = 10'b1011011000;
    assign parity_check_matrix[187] = 10'b1010011010;
    assign parity_check_matrix[188] = 10'b0001111100;
    assign parity_check_matrix[189] = 10'b0001111010;
    assign parity_check_matrix[190] = 10'b0001111001;
    assign parity_check_matrix[191] = 10'b0111110000;
    assign parity_check_matrix[192] = 10'b0101110100;
    assign parity_check_matrix[193] = 10'b0101110010;
    assign parity_check_matrix[194] = 10'b0011110001;
    assign parity_check_matrix[195] = 10'b0001110101;
    assign parity_check_matrix[196] = 10'b0011110010;
    assign parity_check_matrix[197] = 10'b0001101110;
    assign parity_check_matrix[198] = 10'b0001101101;
    assign parity_check_matrix[199] = 10'b0111101000;
    assign parity_check_matrix[200] = 10'b0101101010;
    assign parity_check_matrix[201] = 10'b0011101001;
    assign parity_check_matrix[202] = 10'b0001100111;
    assign parity_check_matrix[203] = 10'b0101100110;
    assign parity_check_matrix[204] = 10'b0011100101;
    assign parity_check_matrix[205] = 10'b0111100001;
    assign parity_check_matrix[206] = 10'b0111100010;
    assign parity_check_matrix[207] = 10'b0001001111;
    assign parity_check_matrix[208] = 10'b0101001110;
    assign parity_check_matrix[209] = 10'b0011001110;
    assign parity_check_matrix[210] = 10'b0001011101;
    assign parity_check_matrix[211] = 10'b0101011100;
    assign parity_check_matrix[212] = 10'b0011001101;
    assign parity_check_matrix[213] = 10'b0101001011;
    assign parity_check_matrix[214] = 10'b0011001011;
    assign parity_check_matrix[215] = 10'b0101011010;
    assign parity_check_matrix[216] = 10'b0111011000;
    assign parity_check_matrix[217] = 10'b0011011001;
    assign parity_check_matrix[218] = 10'b0111000110;
    assign parity_check_matrix[219] = 10'b0111000101;
    assign parity_check_matrix[220] = 10'b0111010001;
    assign parity_check_matrix[221] = 10'b0111010010;
    assign parity_check_matrix[222] = 10'b0101010110;
    assign parity_check_matrix[223] = 10'b0101000111;
    assign parity_check_matrix[224] = 10'b0011010011;
    assign parity_check_matrix[225] = 10'b0011010101;
    assign parity_check_matrix[226] = 10'b0000111110;
    assign parity_check_matrix[227] = 10'b0000111101;
    assign parity_check_matrix[228] = 10'b0100111100;
    assign parity_check_matrix[229] = 10'b0010111010;
    assign parity_check_matrix[230] = 10'b0010111001;
    assign parity_check_matrix[231] = 10'b0100111010;
    assign parity_check_matrix[232] = 10'b0000110111;
    assign parity_check_matrix[233] = 10'b0100110110;
    assign parity_check_matrix[234] = 10'b0010110101;
    assign parity_check_matrix[235] = 10'b0110110001;
    assign parity_check_matrix[236] = 10'b0110110010;
    assign parity_check_matrix[237] = 10'b0100101101;
    assign parity_check_matrix[238] = 10'b0100101011;
    assign parity_check_matrix[239] = 10'b0110100011;
    assign parity_check_matrix[240] = 10'b0110100101;
    assign parity_check_matrix[241] = 10'b0010101101;
    assign parity_check_matrix[242] = 10'b0000101111;
    assign parity_check_matrix[243] = 10'b0110100110;
    assign parity_check_matrix[244] = 10'b0110101010;
    assign parity_check_matrix[245] = 10'b0010011110;
    assign parity_check_matrix[246] = 10'b0010011101;
    assign parity_check_matrix[247] = 10'b0110011001;
    assign parity_check_matrix[248] = 10'b0110011010;
    assign parity_check_matrix[249] = 10'b0110010110;
    assign parity_check_matrix[250] = 10'b0010010111;
    assign parity_check_matrix[251] = 10'b0110001011;
    assign parity_check_matrix[252] = 10'b0110001101;
    assign parity_check_matrix[253] = 10'b0100001111;
    assign parity_check_matrix[254] = 10'b0100010111;
    assign parity_check_matrix[255] = 10'b0000011111;
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
  end else begin : gen_default
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
