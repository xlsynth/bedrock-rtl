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

// Bedrock-RTL Single-Error-Correcting, Double-Error-Detecting (SECDED - Hsiao) Encoder
//
// Encodes a message using a single-error-correcting, double-error-detecting
// linear block code in systematic form (in layperson's terms: a Hsiao SECDED [1] encoder,
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
// This module has parameterizable latency. By default, it is purely combinational,
// but it can have up to 2 cycles of delay (RegisterInputs and RegisterOutputs).
// The initiation interval is always 1 cycle.
//
// Any DataWidth >= 4 is supported, up to a maximum of 256.
// * If DataWidth is a power of 2, it benefits from a specifically generated ECC code construction
//   and the MessageWidth is set to the DataWidth.
// * If DataWidth is not a power of 2, it is internally zero-padded up to the nearest supported MessageWidth
//   before it is encoded.
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

module br_ecc_secded_encoder #(
    parameter int DataWidth = 4,  // Must be at least 4
    parameter int ParityWidth = 4,  // Must be at least 4 and at most 10
    // If 1, then insert a pipeline register at the input.
    parameter bit RegisterInputs = 0,
    // If 1, then insert a pipeline register at the output.
    parameter bit RegisterOutputs = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
    localparam int OutputWidth = DataWidth + ParityWidth,
    localparam int MessageWidth = br_ecc::get_message_width(DataWidth, ParityWidth),
    localparam int CodewordWidth = MessageWidth + ParityWidth
) (
    // Positive edge-triggered clock.
    input  logic                     clk,
    // Synchronous active-high reset.
    input  logic                     rst,
    input  logic                     data_valid,
    input  logic [    DataWidth-1:0] data,
    output logic                     enc_valid,
    output logic [    DataWidth-1:0] enc_data,
    output logic [  ParityWidth-1:0] enc_parity,
    // A concatenation of {enc_parity, 0 padding, enc_data}, i.e.,
    // {enc_parity, message}
    output logic [CodewordWidth-1:0] enc_codeword
);

  // ri lint_check_waive PARAM_NOT_USED
  localparam int Latency = RegisterInputs + RegisterOutputs;

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
  logic data_valid_d;
  logic [DataWidth-1:0] data_d;

  br_delay_valid #(
      .Width(DataWidth),
      .NumStages(RegisterInputs == 1 ? 1 : 0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
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

  //------
  // Pad the data to the message width.
  //------

  localparam int PadWidth = MessageWidth - DataWidth;
  logic [MessageWidth-1:0] m;

  if (PadWidth > 0) begin : gen_pad
    assign m = { {PadWidth{1'b0} }, data_d};
  end else begin : gen_no_pad
    assign m = data_d;
  end

  //------
  // Compute parity bits.
  //------
  logic [ParityWidth-1:0] parity;

  // ri lint_check_off EXPR_ID_LIMIT

  if ((CodewordWidth == 8) && (MessageWidth == 4)) begin : gen_8_4
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 4)
    assign parity[0] = m[1] ^ m[2] ^ m[3];
    assign parity[1] = m[0] ^ m[2] ^ m[3];
    assign parity[2] = m[0] ^ m[1] ^ m[3];
    assign parity[3] = m[0] ^ m[1] ^ m[2];
  end else if ((CodewordWidth == 13) && (MessageWidth == 8)) begin : gen_13_8
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 5)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[6] ^ m[7];
    assign parity[2] = m[0] ^ m[3] ^ m[4] ^ m[5] ^ m[7];
    assign parity[3] = m[1] ^ m[4] ^ m[5] ^ m[6] ^ m[7];
    assign parity[4] = m[2] ^ m[3] ^ m[5] ^ m[6];
  end else if ((CodewordWidth == 16) && (MessageWidth == 11)) begin : gen_16_11
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 5)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[10];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[7] ^ m[8] ^ m[9] ^ m[10];
    assign parity[2] = m[0] ^ m[4] ^ m[5] ^ m[6] ^ m[8] ^ m[9] ^ m[10];
    assign parity[3] = m[1] ^ m[3] ^ m[5] ^ m[6] ^ m[7] ^ m[9] ^ m[10];
    assign parity[4] = m[2] ^ m[3] ^ m[4] ^ m[6] ^ m[7] ^ m[8] ^ m[10];
  end else if ((CodewordWidth == 22) && (MessageWidth == 16)) begin : gen_22_16
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 6)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[10] ^ m[11] ^ m[13] ^ m[14];
    assign parity[2] = m[0] ^ m[4] ^ m[5] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12];
    assign parity[3] = m[1] ^ m[4] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[14] ^ m[15];
    assign parity[4] = m[2] ^ m[5] ^ m[6] ^ m[8] ^ m[11] ^ m[12] ^ m[13] ^ m[15];
    assign parity[5] = m[3] ^ m[6] ^ m[7] ^ m[9] ^ m[12] ^ m[13] ^ m[14] ^ m[15];
  end else if ((CodewordWidth == 32) && (MessageWidth == 26)) begin : gen_32_26
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 6)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[20] ^ m[22] ^ m[23] ^ m[24] ^ m[25];
    assign parity[2] = m[0] ^ m[4] ^ m[5] ^ m[6] ^ m[10] ^ m[11] ^ m[12] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[23] ^ m[24] ^ m[25];
    assign parity[3] = m[1] ^ m[4] ^ m[8] ^ m[9] ^ m[10] ^ m[14] ^ m[15] ^ m[16] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[24] ^ m[25];
    assign parity[4] = m[2] ^ m[5] ^ m[7] ^ m[9] ^ m[11] ^ m[13] ^ m[15] ^ m[16] ^ m[17] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[25];
    assign parity[5] = m[3] ^ m[6] ^ m[7] ^ m[8] ^ m[12] ^ m[13] ^ m[14] ^ m[16] ^ m[17] ^ m[18] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[24];
  end else if ((CodewordWidth == 39) && (MessageWidth == 32)) begin : gen_39_32
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 7)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22];
    assign parity[2] = m[0] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[23] ^ m[27] ^ m[28] ^ m[30] ^ m[31];
    assign parity[3] = m[1] ^ m[5] ^ m[9] ^ m[10] ^ m[11] ^ m[14] ^ m[18] ^ m[19] ^ m[20] ^ m[24] ^ m[26] ^ m[28] ^ m[29] ^ m[31];
    assign parity[4] = m[2] ^ m[6] ^ m[9] ^ m[12] ^ m[13] ^ m[15] ^ m[18] ^ m[21] ^ m[22] ^ m[25] ^ m[26] ^ m[27] ^ m[29] ^ m[30];
    assign parity[5] = m[3] ^ m[7] ^ m[10] ^ m[13] ^ m[16] ^ m[19] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[28];
    assign parity[6] = m[4] ^ m[8] ^ m[11] ^ m[12] ^ m[17] ^ m[20] ^ m[21] ^ m[23] ^ m[24] ^ m[25] ^ m[29] ^ m[30] ^ m[31];
  end else if ((CodewordWidth == 64) && (MessageWidth == 57)) begin : gen_64_57
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 7)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[49] ^ m[56];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[51] ^ m[52] ^ m[53] ^ m[54] ^ m[55] ^ m[56];
    assign parity[2] = m[0] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[25] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[30] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[46] ^ m[47] ^ m[48] ^ m[49] ^ m[50] ^ m[52] ^ m[53] ^ m[54] ^ m[55] ^ m[56];
    assign parity[3] = m[1] ^ m[5] ^ m[9] ^ m[10] ^ m[11] ^ m[15] ^ m[19] ^ m[20] ^ m[21] ^ m[25] ^ m[26] ^ m[27] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[36] ^ m[37] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[47] ^ m[48] ^ m[49] ^ m[50] ^ m[51] ^ m[53] ^ m[54] ^ m[55] ^ m[56];
    assign parity[4] = m[2] ^ m[6] ^ m[9] ^ m[13] ^ m[14] ^ m[16] ^ m[19] ^ m[23] ^ m[24] ^ m[25] ^ m[29] ^ m[30] ^ m[31] ^ m[33] ^ m[34] ^ m[35] ^ m[39] ^ m[40] ^ m[41] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[48] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[54] ^ m[55] ^ m[56];
    assign parity[5] = m[3] ^ m[7] ^ m[10] ^ m[12] ^ m[14] ^ m[17] ^ m[20] ^ m[22] ^ m[24] ^ m[26] ^ m[28] ^ m[30] ^ m[31] ^ m[32] ^ m[34] ^ m[36] ^ m[38] ^ m[40] ^ m[41] ^ m[42] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[55] ^ m[56];
    assign parity[6] = m[4] ^ m[8] ^ m[11] ^ m[12] ^ m[13] ^ m[18] ^ m[21] ^ m[22] ^ m[23] ^ m[27] ^ m[28] ^ m[29] ^ m[31] ^ m[32] ^ m[33] ^ m[37] ^ m[38] ^ m[39] ^ m[41] ^ m[42] ^ m[43] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[54] ^ m[56];
  end else if ((CodewordWidth == 72) && (MessageWidth == 64)) begin : gen_72_64
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 8)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[56] ^ m[57] ^ m[58] ^ m[61] ^ m[62];
    assign parity[2] = m[0] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[56] ^ m[57] ^ m[59] ^ m[61] ^ m[62];
    assign parity[3] = m[1] ^ m[6] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[21] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[46] ^ m[47] ^ m[48] ^ m[49] ^ m[50] ^ m[51] ^ m[56] ^ m[58] ^ m[59] ^ m[61] ^ m[63];
    assign parity[4] = m[2] ^ m[7] ^ m[11] ^ m[15] ^ m[16] ^ m[17] ^ m[22] ^ m[26] ^ m[30] ^ m[31] ^ m[32] ^ m[36] ^ m[40] ^ m[41] ^ m[42] ^ m[46] ^ m[47] ^ m[48] ^ m[53] ^ m[54] ^ m[55] ^ m[56] ^ m[58] ^ m[60] ^ m[61] ^ m[63];
    assign parity[5] = m[3] ^ m[8] ^ m[12] ^ m[15] ^ m[19] ^ m[20] ^ m[23] ^ m[27] ^ m[30] ^ m[34] ^ m[35] ^ m[37] ^ m[40] ^ m[44] ^ m[45] ^ m[46] ^ m[50] ^ m[51] ^ m[52] ^ m[54] ^ m[55] ^ m[57] ^ m[59] ^ m[60] ^ m[62] ^ m[63];
    assign parity[6] = m[4] ^ m[9] ^ m[13] ^ m[16] ^ m[18] ^ m[20] ^ m[24] ^ m[28] ^ m[31] ^ m[33] ^ m[35] ^ m[38] ^ m[41] ^ m[43] ^ m[45] ^ m[47] ^ m[49] ^ m[51] ^ m[52] ^ m[53] ^ m[55] ^ m[57] ^ m[59] ^ m[60] ^ m[62] ^ m[63];
    assign parity[7] = m[5] ^ m[10] ^ m[14] ^ m[17] ^ m[18] ^ m[19] ^ m[25] ^ m[29] ^ m[32] ^ m[33] ^ m[34] ^ m[39] ^ m[42] ^ m[43] ^ m[44] ^ m[48] ^ m[49] ^ m[50] ^ m[52] ^ m[53] ^ m[54] ^ m[58] ^ m[60] ^ m[61] ^ m[62] ^ m[63];
  end else if ((CodewordWidth == 128) && (MessageWidth == 120)) begin : gen_128_120
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 8)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[74] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[80] ^ m[81] ^ m[82] ^ m[83] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[119];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[74] ^ m[75] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[112] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[119];
    assign parity[2] = m[0] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[64] ^ m[65] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[80] ^ m[81] ^ m[82] ^ m[83] ^ m[84] ^ m[85] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[107] ^ m[108] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[119];
    assign parity[3] = m[1] ^ m[6] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[21] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[46] ^ m[47] ^ m[48] ^ m[49] ^ m[50] ^ m[51] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[80] ^ m[81] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[108] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[116] ^ m[117] ^ m[118] ^ m[119];
    assign parity[4] = m[2] ^ m[7] ^ m[11] ^ m[15] ^ m[16] ^ m[17] ^ m[22] ^ m[26] ^ m[30] ^ m[31] ^ m[32] ^ m[36] ^ m[40] ^ m[41] ^ m[42] ^ m[46] ^ m[47] ^ m[48] ^ m[53] ^ m[54] ^ m[55] ^ m[56] ^ m[60] ^ m[61] ^ m[62] ^ m[66] ^ m[67] ^ m[68] ^ m[73] ^ m[74] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[83] ^ m[84] ^ m[85] ^ m[86] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[117] ^ m[118] ^ m[119];
    assign parity[5] = m[3] ^ m[8] ^ m[12] ^ m[15] ^ m[19] ^ m[20] ^ m[23] ^ m[27] ^ m[30] ^ m[34] ^ m[35] ^ m[37] ^ m[40] ^ m[44] ^ m[45] ^ m[46] ^ m[50] ^ m[51] ^ m[52] ^ m[54] ^ m[55] ^ m[57] ^ m[60] ^ m[64] ^ m[65] ^ m[66] ^ m[70] ^ m[71] ^ m[72] ^ m[74] ^ m[75] ^ m[76] ^ m[80] ^ m[81] ^ m[82] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[89] ^ m[90] ^ m[91] ^ m[95] ^ m[96] ^ m[97] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[118] ^ m[119];
    assign parity[6] = m[4] ^ m[9] ^ m[13] ^ m[16] ^ m[18] ^ m[20] ^ m[24] ^ m[28] ^ m[31] ^ m[33] ^ m[35] ^ m[38] ^ m[41] ^ m[43] ^ m[45] ^ m[47] ^ m[49] ^ m[51] ^ m[52] ^ m[53] ^ m[55] ^ m[58] ^ m[61] ^ m[63] ^ m[65] ^ m[67] ^ m[69] ^ m[71] ^ m[72] ^ m[73] ^ m[75] ^ m[77] ^ m[79] ^ m[81] ^ m[82] ^ m[83] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[90] ^ m[92] ^ m[94] ^ m[96] ^ m[97] ^ m[98] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[119];
    assign parity[7] = m[5] ^ m[10] ^ m[14] ^ m[17] ^ m[18] ^ m[19] ^ m[25] ^ m[29] ^ m[32] ^ m[33] ^ m[34] ^ m[39] ^ m[42] ^ m[43] ^ m[44] ^ m[48] ^ m[49] ^ m[50] ^ m[52] ^ m[53] ^ m[54] ^ m[59] ^ m[62] ^ m[63] ^ m[64] ^ m[68] ^ m[69] ^ m[70] ^ m[72] ^ m[73] ^ m[74] ^ m[78] ^ m[79] ^ m[80] ^ m[82] ^ m[83] ^ m[84] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[93] ^ m[94] ^ m[95] ^ m[97] ^ m[98] ^ m[99] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[110] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118];
  end else if ((CodewordWidth == 137) && (MessageWidth == 128)) begin : gen_137_128
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 9)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[109] ^ m[111] ^ m[114] ^ m[115] ^ m[117] ^ m[119] ^ m[120] ^ m[121] ^ m[122] ^ m[124] ^ m[126] ^ m[127];
    assign parity[2] = m[0] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[97] ^ m[99] ^ m[102] ^ m[103] ^ m[105] ^ m[107] ^ m[108] ^ m[110] ^ m[111] ^ m[114] ^ m[116] ^ m[117] ^ m[118] ^ m[119] ^ m[121] ^ m[123] ^ m[125] ^ m[126] ^ m[127];
    assign parity[3] = m[1] ^ m[7] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[28] ^ m[34] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[84] ^ m[85] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[98] ^ m[99] ^ m[102] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[112] ^ m[113] ^ m[114] ^ m[116] ^ m[117] ^ m[118] ^ m[120] ^ m[122] ^ m[124] ^ m[125] ^ m[126] ^ m[127];
    assign parity[4] = m[2] ^ m[8] ^ m[13] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[29] ^ m[34] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[49] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[74] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[84] ^ m[89] ^ m[90] ^ m[91] ^ m[94] ^ m[96] ^ m[100] ^ m[101] ^ m[102] ^ m[104] ^ m[105] ^ m[106] ^ m[108] ^ m[112] ^ m[113] ^ m[115] ^ m[118] ^ m[119] ^ m[120] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127];
    assign parity[5] = m[3] ^ m[9] ^ m[14] ^ m[18] ^ m[22] ^ m[23] ^ m[24] ^ m[30] ^ m[35] ^ m[39] ^ m[43] ^ m[44] ^ m[45] ^ m[50] ^ m[54] ^ m[58] ^ m[59] ^ m[60] ^ m[64] ^ m[68] ^ m[69] ^ m[70] ^ m[74] ^ m[75] ^ m[76] ^ m[81] ^ m[82] ^ m[83] ^ m[85] ^ m[89] ^ m[90] ^ m[92] ^ m[95] ^ m[96] ^ m[100] ^ m[101] ^ m[103] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[119] ^ m[120];
    assign parity[6] = m[4] ^ m[10] ^ m[15] ^ m[19] ^ m[22] ^ m[26] ^ m[27] ^ m[31] ^ m[36] ^ m[40] ^ m[43] ^ m[47] ^ m[48] ^ m[51] ^ m[55] ^ m[58] ^ m[62] ^ m[63] ^ m[65] ^ m[68] ^ m[72] ^ m[73] ^ m[74] ^ m[78] ^ m[79] ^ m[80] ^ m[82] ^ m[83] ^ m[86] ^ m[87] ^ m[91] ^ m[92] ^ m[95] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125];
    assign parity[7] = m[5] ^ m[11] ^ m[16] ^ m[20] ^ m[23] ^ m[25] ^ m[27] ^ m[32] ^ m[37] ^ m[41] ^ m[44] ^ m[46] ^ m[48] ^ m[52] ^ m[56] ^ m[59] ^ m[61] ^ m[63] ^ m[66] ^ m[69] ^ m[71] ^ m[73] ^ m[75] ^ m[77] ^ m[79] ^ m[80] ^ m[81] ^ m[83] ^ m[86] ^ m[88] ^ m[93] ^ m[94] ^ m[95] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[104] ^ m[105] ^ m[107] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[116] ^ m[117] ^ m[119] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[127];
    assign parity[8] = m[6] ^ m[12] ^ m[17] ^ m[21] ^ m[24] ^ m[25] ^ m[26] ^ m[33] ^ m[38] ^ m[42] ^ m[45] ^ m[46] ^ m[47] ^ m[53] ^ m[57] ^ m[60] ^ m[61] ^ m[62] ^ m[67] ^ m[70] ^ m[71] ^ m[72] ^ m[76] ^ m[77] ^ m[78] ^ m[80] ^ m[81] ^ m[82] ^ m[87] ^ m[88] ^ m[93] ^ m[94] ^ m[96] ^ m[97] ^ m[98] ^ m[101] ^ m[103] ^ m[104] ^ m[106] ^ m[108] ^ m[109] ^ m[110] ^ m[113] ^ m[115] ^ m[116] ^ m[118] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[125] ^ m[126];
  end else if ((CodewordWidth == 256) && (MessageWidth == 247)) begin : gen_256_247
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 9)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[119] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[129] ^ m[130] ^ m[131] ^ m[132] ^ m[133] ^ m[134] ^ m[135] ^ m[136] ^ m[137] ^ m[138] ^ m[139] ^ m[140] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[145] ^ m[146] ^ m[147] ^ m[148] ^ m[149] ^ m[150] ^ m[151] ^ m[152] ^ m[153] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[237] ^ m[246];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[116] ^ m[117] ^ m[118] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[164] ^ m[165] ^ m[166] ^ m[167] ^ m[168] ^ m[169] ^ m[170] ^ m[171] ^ m[172] ^ m[173] ^ m[174] ^ m[175] ^ m[176] ^ m[177] ^ m[178] ^ m[179] ^ m[180] ^ m[181] ^ m[182] ^ m[183] ^ m[184] ^ m[185] ^ m[186] ^ m[187] ^ m[188] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[244] ^ m[245] ^ m[246];
    assign parity[2] = m[0] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[119] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[129] ^ m[130] ^ m[131] ^ m[132] ^ m[133] ^ m[134] ^ m[135] ^ m[136] ^ m[137] ^ m[138] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[164] ^ m[165] ^ m[166] ^ m[167] ^ m[168] ^ m[169] ^ m[170] ^ m[171] ^ m[172] ^ m[173] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[195] ^ m[196] ^ m[197] ^ m[198] ^ m[199] ^ m[200] ^ m[201] ^ m[202] ^ m[203] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[244] ^ m[245] ^ m[246];
    assign parity[3] = m[1] ^ m[7] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[28] ^ m[34] ^ m[35] ^ m[36] ^ m[37] ^ m[38] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[84] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[119] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[139] ^ m[140] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[145] ^ m[146] ^ m[147] ^ m[148] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[174] ^ m[175] ^ m[176] ^ m[177] ^ m[178] ^ m[179] ^ m[180] ^ m[181] ^ m[182] ^ m[183] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[195] ^ m[196] ^ m[197] ^ m[198] ^ m[205] ^ m[206] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[241] ^ m[242] ^ m[243] ^ m[244] ^ m[245] ^ m[246];
    assign parity[4] = m[2] ^ m[8] ^ m[13] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[29] ^ m[34] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[49] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[74] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[84] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[99] ^ m[100] ^ m[101] ^ m[102] ^ m[109] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[119] ^ m[120] ^ m[121] ^ m[122] ^ m[129] ^ m[130] ^ m[131] ^ m[132] ^ m[133] ^ m[134] ^ m[139] ^ m[140] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[150] ^ m[151] ^ m[152] ^ m[153] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[164] ^ m[165] ^ m[166] ^ m[167] ^ m[168] ^ m[169] ^ m[174] ^ m[175] ^ m[176] ^ m[177] ^ m[178] ^ m[179] ^ m[185] ^ m[186] ^ m[187] ^ m[188] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[200] ^ m[201] ^ m[202] ^ m[203] ^ m[204] ^ m[206] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[225] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[234] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[242] ^ m[243] ^ m[244] ^ m[245] ^ m[246];
    assign parity[5] = m[3] ^ m[9] ^ m[14] ^ m[18] ^ m[22] ^ m[23] ^ m[24] ^ m[30] ^ m[35] ^ m[39] ^ m[43] ^ m[44] ^ m[45] ^ m[50] ^ m[54] ^ m[58] ^ m[59] ^ m[60] ^ m[64] ^ m[68] ^ m[69] ^ m[70] ^ m[74] ^ m[75] ^ m[76] ^ m[81] ^ m[82] ^ m[83] ^ m[85] ^ m[89] ^ m[93] ^ m[94] ^ m[95] ^ m[99] ^ m[103] ^ m[104] ^ m[105] ^ m[109] ^ m[110] ^ m[111] ^ m[116] ^ m[117] ^ m[118] ^ m[119] ^ m[123] ^ m[124] ^ m[125] ^ m[129] ^ m[130] ^ m[131] ^ m[136] ^ m[137] ^ m[138] ^ m[139] ^ m[140] ^ m[141] ^ m[146] ^ m[147] ^ m[148] ^ m[149] ^ m[151] ^ m[152] ^ m[153] ^ m[154] ^ m[158] ^ m[159] ^ m[160] ^ m[164] ^ m[165] ^ m[166] ^ m[171] ^ m[172] ^ m[173] ^ m[174] ^ m[175] ^ m[176] ^ m[181] ^ m[182] ^ m[183] ^ m[184] ^ m[186] ^ m[187] ^ m[188] ^ m[189] ^ m[190] ^ m[191] ^ m[196] ^ m[197] ^ m[198] ^ m[199] ^ m[201] ^ m[202] ^ m[203] ^ m[204] ^ m[205] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[222] ^ m[223] ^ m[224] ^ m[225] ^ m[226] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[243] ^ m[244] ^ m[245] ^ m[246];
    assign parity[6] = m[4] ^ m[10] ^ m[15] ^ m[19] ^ m[22] ^ m[26] ^ m[27] ^ m[31] ^ m[36] ^ m[40] ^ m[43] ^ m[47] ^ m[48] ^ m[51] ^ m[55] ^ m[58] ^ m[62] ^ m[63] ^ m[65] ^ m[68] ^ m[72] ^ m[73] ^ m[74] ^ m[78] ^ m[79] ^ m[80] ^ m[82] ^ m[83] ^ m[86] ^ m[90] ^ m[93] ^ m[97] ^ m[98] ^ m[100] ^ m[103] ^ m[107] ^ m[108] ^ m[109] ^ m[113] ^ m[114] ^ m[115] ^ m[117] ^ m[118] ^ m[120] ^ m[123] ^ m[127] ^ m[128] ^ m[129] ^ m[133] ^ m[134] ^ m[135] ^ m[137] ^ m[138] ^ m[139] ^ m[143] ^ m[144] ^ m[145] ^ m[147] ^ m[148] ^ m[149] ^ m[150] ^ m[152] ^ m[153] ^ m[155] ^ m[158] ^ m[162] ^ m[163] ^ m[164] ^ m[168] ^ m[169] ^ m[170] ^ m[172] ^ m[173] ^ m[174] ^ m[178] ^ m[179] ^ m[180] ^ m[182] ^ m[183] ^ m[184] ^ m[185] ^ m[187] ^ m[188] ^ m[189] ^ m[193] ^ m[194] ^ m[195] ^ m[197] ^ m[198] ^ m[199] ^ m[200] ^ m[202] ^ m[203] ^ m[204] ^ m[205] ^ m[206] ^ m[208] ^ m[209] ^ m[210] ^ m[214] ^ m[215] ^ m[216] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[223] ^ m[224] ^ m[225] ^ m[226] ^ m[227] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[244] ^ m[245] ^ m[246];
    assign parity[7] = m[5] ^ m[11] ^ m[16] ^ m[20] ^ m[23] ^ m[25] ^ m[27] ^ m[32] ^ m[37] ^ m[41] ^ m[44] ^ m[46] ^ m[48] ^ m[52] ^ m[56] ^ m[59] ^ m[61] ^ m[63] ^ m[66] ^ m[69] ^ m[71] ^ m[73] ^ m[75] ^ m[77] ^ m[79] ^ m[80] ^ m[81] ^ m[83] ^ m[87] ^ m[91] ^ m[94] ^ m[96] ^ m[98] ^ m[101] ^ m[104] ^ m[106] ^ m[108] ^ m[110] ^ m[112] ^ m[114] ^ m[115] ^ m[116] ^ m[118] ^ m[121] ^ m[124] ^ m[126] ^ m[128] ^ m[130] ^ m[132] ^ m[134] ^ m[135] ^ m[136] ^ m[138] ^ m[140] ^ m[142] ^ m[144] ^ m[145] ^ m[146] ^ m[148] ^ m[149] ^ m[150] ^ m[151] ^ m[153] ^ m[156] ^ m[159] ^ m[161] ^ m[163] ^ m[165] ^ m[167] ^ m[169] ^ m[170] ^ m[171] ^ m[173] ^ m[175] ^ m[177] ^ m[179] ^ m[180] ^ m[181] ^ m[183] ^ m[184] ^ m[185] ^ m[186] ^ m[188] ^ m[190] ^ m[192] ^ m[194] ^ m[195] ^ m[196] ^ m[198] ^ m[199] ^ m[200] ^ m[201] ^ m[203] ^ m[204] ^ m[205] ^ m[206] ^ m[207] ^ m[209] ^ m[211] ^ m[213] ^ m[215] ^ m[216] ^ m[217] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[224] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[245] ^ m[246];
    assign parity[8] = m[6] ^ m[12] ^ m[17] ^ m[21] ^ m[24] ^ m[25] ^ m[26] ^ m[33] ^ m[38] ^ m[42] ^ m[45] ^ m[46] ^ m[47] ^ m[53] ^ m[57] ^ m[60] ^ m[61] ^ m[62] ^ m[67] ^ m[70] ^ m[71] ^ m[72] ^ m[76] ^ m[77] ^ m[78] ^ m[80] ^ m[81] ^ m[82] ^ m[88] ^ m[92] ^ m[95] ^ m[96] ^ m[97] ^ m[102] ^ m[105] ^ m[106] ^ m[107] ^ m[111] ^ m[112] ^ m[113] ^ m[115] ^ m[116] ^ m[117] ^ m[122] ^ m[125] ^ m[126] ^ m[127] ^ m[131] ^ m[132] ^ m[133] ^ m[135] ^ m[136] ^ m[137] ^ m[141] ^ m[142] ^ m[143] ^ m[145] ^ m[146] ^ m[147] ^ m[149] ^ m[150] ^ m[151] ^ m[152] ^ m[157] ^ m[160] ^ m[161] ^ m[162] ^ m[166] ^ m[167] ^ m[168] ^ m[170] ^ m[171] ^ m[172] ^ m[176] ^ m[177] ^ m[178] ^ m[180] ^ m[181] ^ m[182] ^ m[184] ^ m[185] ^ m[186] ^ m[187] ^ m[191] ^ m[192] ^ m[193] ^ m[195] ^ m[196] ^ m[197] ^ m[199] ^ m[200] ^ m[201] ^ m[202] ^ m[204] ^ m[205] ^ m[206] ^ m[207] ^ m[208] ^ m[212] ^ m[213] ^ m[214] ^ m[216] ^ m[217] ^ m[218] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[244] ^ m[246];
  end else if ((CodewordWidth == 266) && (MessageWidth == 256)) begin : gen_266_256
    `BR_ASSERT_STATIC(parity_width_matches_a, ParityWidth == 10)
    assign parity[0] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[30] ^ m[31] ^ m[32] ^ m[33] ^ m[34] ^ m[35] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[129] ^ m[130] ^ m[131] ^ m[132] ^ m[133] ^ m[134] ^ m[135] ^ m[136] ^ m[137] ^ m[138] ^ m[139] ^ m[140] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[145] ^ m[146] ^ m[147] ^ m[148] ^ m[149] ^ m[150] ^ m[151] ^ m[152] ^ m[153] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[164] ^ m[165] ^ m[166] ^ m[167] ^ m[168] ^ m[169] ^ m[170] ^ m[171] ^ m[172] ^ m[173] ^ m[174] ^ m[175] ^ m[176] ^ m[177] ^ m[178] ^ m[179] ^ m[180] ^ m[181] ^ m[182] ^ m[183] ^ m[184] ^ m[185] ^ m[186] ^ m[187];
    assign parity[1] = m[0] ^ m[1] ^ m[2] ^ m[3] ^ m[4] ^ m[5] ^ m[6] ^ m[7] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[58] ^ m[59] ^ m[60] ^ m[61] ^ m[62] ^ m[63] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[129] ^ m[130] ^ m[131] ^ m[132] ^ m[133] ^ m[134] ^ m[135] ^ m[136] ^ m[137] ^ m[138] ^ m[139] ^ m[140] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[145] ^ m[146] ^ m[147] ^ m[148] ^ m[149] ^ m[150] ^ m[191] ^ m[192] ^ m[193] ^ m[199] ^ m[200] ^ m[203] ^ m[205] ^ m[206] ^ m[208] ^ m[211] ^ m[213] ^ m[215] ^ m[216] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[228] ^ m[231] ^ m[233] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[243] ^ m[244] ^ m[247] ^ m[248] ^ m[249] ^ m[251] ^ m[252] ^ m[253] ^ m[254];
    assign parity[2] = m[0] ^ m[8] ^ m[9] ^ m[10] ^ m[11] ^ m[12] ^ m[13] ^ m[14] ^ m[36] ^ m[37] ^ m[38] ^ m[39] ^ m[40] ^ m[41] ^ m[42] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[74] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[79] ^ m[80] ^ m[81] ^ m[82] ^ m[83] ^ m[84] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[124] ^ m[125] ^ m[126] ^ m[127] ^ m[128] ^ m[129] ^ m[130] ^ m[131] ^ m[151] ^ m[155] ^ m[158] ^ m[160] ^ m[161] ^ m[165] ^ m[166] ^ m[167] ^ m[170] ^ m[171] ^ m[172] ^ m[173] ^ m[174] ^ m[175] ^ m[181] ^ m[183] ^ m[184] ^ m[186] ^ m[187] ^ m[191] ^ m[194] ^ m[196] ^ m[199] ^ m[201] ^ m[204] ^ m[205] ^ m[206] ^ m[209] ^ m[212] ^ m[214] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[224] ^ m[225] ^ m[229] ^ m[230] ^ m[234] ^ m[235] ^ m[236] ^ m[239] ^ m[240] ^ m[241] ^ m[243] ^ m[244] ^ m[245] ^ m[246] ^ m[247] ^ m[248] ^ m[249] ^ m[250] ^ m[251] ^ m[252];
    assign parity[3] = m[1] ^ m[8] ^ m[15] ^ m[16] ^ m[17] ^ m[18] ^ m[19] ^ m[20] ^ m[36] ^ m[43] ^ m[44] ^ m[45] ^ m[46] ^ m[47] ^ m[48] ^ m[64] ^ m[65] ^ m[66] ^ m[67] ^ m[68] ^ m[69] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[94] ^ m[95] ^ m[96] ^ m[97] ^ m[98] ^ m[99] ^ m[120] ^ m[121] ^ m[122] ^ m[123] ^ m[132] ^ m[133] ^ m[134] ^ m[141] ^ m[142] ^ m[143] ^ m[144] ^ m[145] ^ m[152] ^ m[156] ^ m[159] ^ m[160] ^ m[163] ^ m[165] ^ m[166] ^ m[169] ^ m[170] ^ m[173] ^ m[175] ^ m[176] ^ m[177] ^ m[180] ^ m[183] ^ m[184] ^ m[185] ^ m[186] ^ m[188] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[195] ^ m[196] ^ m[197] ^ m[198] ^ m[199] ^ m[200] ^ m[201] ^ m[202] ^ m[203] ^ m[204] ^ m[205] ^ m[206] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[218] ^ m[219] ^ m[220] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[225];
    assign parity[4] = m[2] ^ m[9] ^ m[15] ^ m[21] ^ m[22] ^ m[23] ^ m[24] ^ m[25] ^ m[37] ^ m[43] ^ m[49] ^ m[50] ^ m[51] ^ m[52] ^ m[53] ^ m[64] ^ m[70] ^ m[71] ^ m[72] ^ m[73] ^ m[74] ^ m[85] ^ m[86] ^ m[87] ^ m[88] ^ m[89] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[104] ^ m[105] ^ m[106] ^ m[107] ^ m[108] ^ m[109] ^ m[120] ^ m[125] ^ m[127] ^ m[130] ^ m[132] ^ m[136] ^ m[139] ^ m[141] ^ m[142] ^ m[146] ^ m[147] ^ m[148] ^ m[153] ^ m[157] ^ m[158] ^ m[161] ^ m[164] ^ m[165] ^ m[167] ^ m[168] ^ m[171] ^ m[174] ^ m[176] ^ m[178] ^ m[179] ^ m[181] ^ m[182] ^ m[183] ^ m[184] ^ m[185] ^ m[188] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[195] ^ m[196] ^ m[197] ^ m[198] ^ m[199] ^ m[200] ^ m[201] ^ m[202] ^ m[203] ^ m[204] ^ m[205] ^ m[206] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[244];
    assign parity[5] = m[3] ^ m[10] ^ m[16] ^ m[21] ^ m[26] ^ m[27] ^ m[28] ^ m[29] ^ m[38] ^ m[44] ^ m[49] ^ m[54] ^ m[55] ^ m[56] ^ m[57] ^ m[65] ^ m[70] ^ m[75] ^ m[76] ^ m[77] ^ m[78] ^ m[85] ^ m[90] ^ m[91] ^ m[92] ^ m[93] ^ m[100] ^ m[101] ^ m[102] ^ m[103] ^ m[110] ^ m[111] ^ m[112] ^ m[113] ^ m[114] ^ m[115] ^ m[121] ^ m[126] ^ m[128] ^ m[131] ^ m[133] ^ m[137] ^ m[140] ^ m[141] ^ m[144] ^ m[146] ^ m[147] ^ m[150] ^ m[154] ^ m[155] ^ m[156] ^ m[162] ^ m[163] ^ m[166] ^ m[168] ^ m[169] ^ m[172] ^ m[175] ^ m[177] ^ m[179] ^ m[180] ^ m[181] ^ m[182] ^ m[183] ^ m[186] ^ m[187] ^ m[188] ^ m[189] ^ m[190] ^ m[191] ^ m[192] ^ m[193] ^ m[194] ^ m[195] ^ m[196] ^ m[210] ^ m[211] ^ m[215] ^ m[216] ^ m[217] ^ m[220] ^ m[221] ^ m[222] ^ m[224] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[232] ^ m[233] ^ m[234] ^ m[235] ^ m[236] ^ m[245] ^ m[246] ^ m[247] ^ m[248] ^ m[249] ^ m[250] ^ m[254] ^ m[255];
    assign parity[6] = m[4] ^ m[11] ^ m[17] ^ m[22] ^ m[26] ^ m[30] ^ m[31] ^ m[32] ^ m[39] ^ m[45] ^ m[50] ^ m[54] ^ m[58] ^ m[59] ^ m[60] ^ m[66] ^ m[71] ^ m[75] ^ m[79] ^ m[80] ^ m[81] ^ m[86] ^ m[90] ^ m[94] ^ m[95] ^ m[96] ^ m[100] ^ m[104] ^ m[105] ^ m[106] ^ m[110] ^ m[111] ^ m[112] ^ m[117] ^ m[118] ^ m[119] ^ m[122] ^ m[129] ^ m[130] ^ m[132] ^ m[133] ^ m[134] ^ m[135] ^ m[136] ^ m[137] ^ m[138] ^ m[139] ^ m[140] ^ m[154] ^ m[157] ^ m[159] ^ m[162] ^ m[164] ^ m[167] ^ m[168] ^ m[169] ^ m[173] ^ m[174] ^ m[178] ^ m[179] ^ m[180] ^ m[181] ^ m[182] ^ m[185] ^ m[186] ^ m[187] ^ m[188] ^ m[189] ^ m[190] ^ m[197] ^ m[198] ^ m[199] ^ m[200] ^ m[201] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[213] ^ m[214] ^ m[215] ^ m[216] ^ m[217] ^ m[226] ^ m[227] ^ m[228] ^ m[229] ^ m[230] ^ m[231] ^ m[237] ^ m[238] ^ m[241] ^ m[242] ^ m[244] ^ m[245] ^ m[246] ^ m[247] ^ m[248] ^ m[251] ^ m[252] ^ m[253] ^ m[255];
    assign parity[7] = m[5] ^ m[12] ^ m[18] ^ m[23] ^ m[27] ^ m[30] ^ m[34] ^ m[35] ^ m[40] ^ m[46] ^ m[51] ^ m[55] ^ m[58] ^ m[62] ^ m[63] ^ m[67] ^ m[72] ^ m[76] ^ m[79] ^ m[83] ^ m[84] ^ m[87] ^ m[91] ^ m[94] ^ m[98] ^ m[99] ^ m[101] ^ m[104] ^ m[108] ^ m[109] ^ m[110] ^ m[114] ^ m[115] ^ m[116] ^ m[118] ^ m[119] ^ m[123] ^ m[129] ^ m[131] ^ m[134] ^ m[138] ^ m[139] ^ m[142] ^ m[145] ^ m[146] ^ m[148] ^ m[149] ^ m[151] ^ m[152] ^ m[153] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[164] ^ m[165] ^ m[166] ^ m[167] ^ m[168] ^ m[169] ^ m[188] ^ m[192] ^ m[195] ^ m[197] ^ m[198] ^ m[202] ^ m[203] ^ m[204] ^ m[207] ^ m[208] ^ m[209] ^ m[210] ^ m[211] ^ m[212] ^ m[218] ^ m[219] ^ m[222] ^ m[223] ^ m[225] ^ m[226] ^ m[227] ^ m[228] ^ m[232] ^ m[233] ^ m[234] ^ m[237] ^ m[240] ^ m[241] ^ m[242] ^ m[243] ^ m[245] ^ m[246] ^ m[249] ^ m[250] ^ m[252] ^ m[253] ^ m[254] ^ m[255];
    assign parity[8] = m[6] ^ m[13] ^ m[19] ^ m[24] ^ m[28] ^ m[31] ^ m[33] ^ m[35] ^ m[41] ^ m[47] ^ m[52] ^ m[56] ^ m[59] ^ m[61] ^ m[63] ^ m[68] ^ m[73] ^ m[77] ^ m[80] ^ m[82] ^ m[84] ^ m[88] ^ m[92] ^ m[95] ^ m[97] ^ m[99] ^ m[102] ^ m[105] ^ m[107] ^ m[109] ^ m[111] ^ m[113] ^ m[115] ^ m[116] ^ m[117] ^ m[119] ^ m[124] ^ m[125] ^ m[126] ^ m[135] ^ m[136] ^ m[137] ^ m[143] ^ m[144] ^ m[147] ^ m[149] ^ m[150] ^ m[151] ^ m[152] ^ m[153] ^ m[154] ^ m[155] ^ m[156] ^ m[157] ^ m[158] ^ m[159] ^ m[170] ^ m[171] ^ m[172] ^ m[176] ^ m[177] ^ m[178] ^ m[182] ^ m[184] ^ m[185] ^ m[187] ^ m[189] ^ m[193] ^ m[196] ^ m[197] ^ m[200] ^ m[202] ^ m[203] ^ m[206] ^ m[207] ^ m[208] ^ m[209] ^ m[213] ^ m[214] ^ m[215] ^ m[218] ^ m[221] ^ m[222] ^ m[223] ^ m[224] ^ m[226] ^ m[229] ^ m[231] ^ m[232] ^ m[233] ^ m[236] ^ m[238] ^ m[239] ^ m[242] ^ m[243] ^ m[244] ^ m[245] ^ m[248] ^ m[249] ^ m[250] ^ m[251] ^ m[253] ^ m[254] ^ m[255];
    assign parity[9] = m[7] ^ m[14] ^ m[20] ^ m[25] ^ m[29] ^ m[32] ^ m[33] ^ m[34] ^ m[42] ^ m[48] ^ m[53] ^ m[57] ^ m[60] ^ m[61] ^ m[62] ^ m[69] ^ m[74] ^ m[78] ^ m[81] ^ m[82] ^ m[83] ^ m[89] ^ m[93] ^ m[96] ^ m[97] ^ m[98] ^ m[103] ^ m[106] ^ m[107] ^ m[108] ^ m[112] ^ m[113] ^ m[114] ^ m[116] ^ m[117] ^ m[118] ^ m[124] ^ m[127] ^ m[128] ^ m[135] ^ m[138] ^ m[140] ^ m[143] ^ m[145] ^ m[148] ^ m[149] ^ m[150] ^ m[151] ^ m[152] ^ m[153] ^ m[160] ^ m[161] ^ m[162] ^ m[163] ^ m[164] ^ m[170] ^ m[171] ^ m[172] ^ m[173] ^ m[174] ^ m[175] ^ m[176] ^ m[177] ^ m[178] ^ m[179] ^ m[180] ^ m[190] ^ m[194] ^ m[195] ^ m[198] ^ m[201] ^ m[202] ^ m[204] ^ m[205] ^ m[207] ^ m[210] ^ m[212] ^ m[213] ^ m[214] ^ m[217] ^ m[219] ^ m[220] ^ m[223] ^ m[224] ^ m[225] ^ m[227] ^ m[230] ^ m[232] ^ m[234] ^ m[235] ^ m[237] ^ m[238] ^ m[239] ^ m[240] ^ m[241] ^ m[242] ^ m[246] ^ m[247] ^ m[250] ^ m[251] ^ m[252] ^ m[253] ^ m[254] ^ m[255];
  end else begin : gen_default
    `BR_ASSERT_STATIC(invalid_parity_width_a, 1'b0)
  end

  // ri lint_check_on EXPR_ID_LIMIT

  //------
  // Concatenate message and parity bits to form the codeword.
  //------
  logic [CodewordWidth-1:0] internal_codeword;
  assign internal_codeword = {parity, m};

  //------
  // Optionally register the output signals.
  //------
  br_delay_valid #(
      .Width(CodewordWidth),
      .NumStages(RegisterOutputs == 1 ? 1 : 0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_outputs (
      .clk,
      .rst,
      .in_valid(data_valid_d),
      .in({internal_codeword}),
      .out_valid(enc_valid),
      .out(enc_codeword),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  //------
  // Drop pad bits
  //------
  assign `BR_TRUNCATE_FROM_LSB(enc_data, enc_codeword)
  assign `BR_TRUNCATE_FROM_MSB(enc_parity, enc_codeword)
  if (OutputWidth < CodewordWidth) begin : gen_unused_out
    `BR_UNUSED_NAMED(unused_out, enc_codeword[MessageWidth-1 : DataWidth])
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(latency_a, data_valid |-> ##Latency enc_valid)

  // verilog_lint: waive-stop line-length
  // verilog_format: on

endmodule : br_ecc_secded_encoder
