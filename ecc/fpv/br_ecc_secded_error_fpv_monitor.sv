// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Single-Error-Correcting, Double-Error-Detecting (SECDED - Hsiao)
// This FV TB focuses on:
//      single error correction
//      double error detection

// | DataWidth   | ParityWidth (r) | MessageWidth (k) | CodewordWidth (n = k + r) | Optimal Construction? |
// |-------------|-----------------|------------------|---------------------------|-----------------------|
// | 4           | 4               | 4                | 8                         | Yes                   |
// | [5,8]       | 5               | 8                | 13                        | Yes                   |
// | [9,11]      | 5               | 11               | 16                        | Yes                   |
// | [12,16]     | 6               | 16               | 22                        | Yes                   |
// | [17,26]     | 6               | 26               | 32                        | Yes                   |
// | [27,32]     | 7               | 32               | 39                        | Yes                   |
// | [33,57]     | 7               | 57               | 64                        | Yes                   |
// | [58,64]     | 8               | 64               | 72                        | Yes                   |
// | [65,120]    | 8               | 120              | 128                       | Yes                   |
// | [121,128]   | 9               | 128              | 137                       | Yes                   |
// | [129,247]   | 9               | 247              | 256                       | Yes                   |
// | [248,256]   | 10              | 256              | 266                       | Yes                   |
// | [257,502]   | 10              | 502              | 512                       | No                    |
// | [503,512]   | 11              | 512              | 523                       | No                    |
// | [513,1013]  | 11              | 1013             | 1024                      | No                    |
// | [1014,1024] | 12              | 1024             | 1036                      | No                    |

`include "br_asserts.svh"
`include "br_registers.svh"
`include "br_fv.svh"

module br_ecc_secded_error_fpv_monitor #(
    parameter int DataWidth = 4,
    parameter bit EncRegisterInputs = 0,
    parameter bit EncRegisterOutputs = 0,
    parameter bit DecRegisterInputs = 0,
    parameter bit DecRegisterOutputs = 0,
    parameter bit RegisterSyndrome = 0,
    localparam int ParityWidth = br_ecc_secded::get_parity_width(DataWidth),
    localparam int InputWidth = DataWidth + ParityWidth,
    localparam int MessageWidth = br_ecc_secded::get_message_width(DataWidth, ParityWidth),
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
  // decoder inputs
  logic [    DataWidth-1:0] se_rcv_data;
  logic [  ParityWidth-1:0] se_rcv_parity;
  logic [    DataWidth-1:0] de_rcv_data;
  logic [  ParityWidth-1:0] de_rcv_parity;
  logic [    DataWidth-1:0] te_rcv_data;
  logic [  ParityWidth-1:0] te_rcv_parity;
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
  // decoder outputs with triple error
  logic                     te_dec_valid;
  logic [   InputWidth-1:0] te_dec_codeword;
  logic                     te_dec_error_ce;  // corrected error
  logic                     te_dec_error_due;  // detected-but-uncorrectable error
  logic [  ParityWidth-1:0] te_dec_error_syndrome;
  logic [    DataWidth-1:0] te_dec_data;
  // FV signals
  logic [   InputWidth-1:0] rcv_codeword;
  logic [   InputWidth-1:0] se_rcv_codeword;  // 1 bit flipped
  logic [   InputWidth-1:0] de_rcv_codeword;  // 2 bits flipped
  logic [   InputWidth-1:0] te_rcv_codeword;  // 3 bits flipped

  // ----------Instantiate br_ecc_secded_encoder----------
  br_ecc_secded_encoder #(
      .DataWidth(DataWidth),
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

  // Pass in codeword with 2 bits flipped
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
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

  // Pass in codeword with 3 bits flipped
  br_ecc_secded_decoder #(
      .DataWidth(DataWidth),
      .RegisterInputs(DecRegisterInputs),
      .RegisterSyndrome(RegisterSyndrome),
      .RegisterOutputs(DecRegisterOutputs)
  ) te_decoder (
      .clk,
      .rst,
      .rcv_valid(enc_valid),
      .rcv_data(te_rcv_data),
      .rcv_parity(te_rcv_parity),
      .dec_valid(te_dec_valid),
      .dec_codeword(te_dec_codeword),
      .dec_error_ce(te_dec_error_ce),
      .dec_error_due(te_dec_error_due),
      .dec_error_syndrome(te_dec_error_syndrome),
      .dec_data(te_dec_data)
  );

  // ----------FV modeling----------
  assign rcv_codeword  = {enc_parity, enc_data};
  assign se_rcv_data   = se_rcv_codeword[DataWidth-1:0];
  assign se_rcv_parity = se_rcv_codeword[InputWidth-1:DataWidth];
  assign de_rcv_data   = de_rcv_codeword[DataWidth-1:0];
  assign de_rcv_parity = de_rcv_codeword[InputWidth-1:DataWidth];
  assign te_rcv_data   = te_rcv_codeword[DataWidth-1:0];
  assign te_rcv_parity = te_rcv_codeword[InputWidth-1:DataWidth];

  // ----------FV assumptions----------
  `BR_ASSUME(se_rcv_codeword_a, $countones(se_rcv_codeword ^ rcv_codeword) == 1)
  `BR_ASSUME(de_rcv_codeword_a, $countones(de_rcv_codeword ^ rcv_codeword) == 2)
  `BR_ASSUME(te_rcv_codeword_a, $countones(te_rcv_codeword ^ rcv_codeword) == 3)

  // ----------FV assertions----------
  if (Latency == 0) begin : gen_latency0
    `BR_ASSERT(se_data_integrity_a, se_dec_valid |-> se_dec_data == data)
    `BR_ASSERT(se_cw_integrity_a, de_dec_valid |-> se_dec_codeword == {enc_parity, data})
  end else begin : gen_latency_non0
    `BR_ASSERT(se_data_integrity_a, se_dec_valid |-> se_dec_data == $past(data, Latency))
    `BR_ASSERT(se_cw_data_integrity_a,
               de_dec_valid |-> se_dec_codeword[DataWidth-1:0] == $past(data, Latency))
  end

  if (DecLatency != 0) begin : gen_parity_ast
    `BR_ASSERT(se_cw_parity_integrity_a,
               de_dec_valid |-> se_dec_codeword[CodewordWidth-1:DataWidth] == $past(
                   enc_parity, DecLatency
               ))
  end

  // single bit flip is detectable and correctable
  `BR_ASSERT(single_error_check_a, se_dec_valid |-> se_dec_error_ce && !se_dec_error_due)
  // double bit flip is detectable and not correctable
  `BR_ASSERT(double_error_check_a, de_dec_valid |-> !de_dec_error_ce && de_dec_error_due)
  // triple bit flip is unpredictable, but it should not be totally silent
  `BR_ASSERT(triple_error_check_a, te_dec_valid |-> (te_dec_error_ce | te_dec_error_due))

endmodule : br_ecc_secded_error_fpv_monitor
