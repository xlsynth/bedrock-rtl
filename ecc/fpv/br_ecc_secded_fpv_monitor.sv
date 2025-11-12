// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Single-Error-Correcting, Double-Error-Detecting (SECDED - Hsiao)
// This FV TB focuses on:
//      basic protocols
//      encoder has no encoding error
//      decoder can correctly decode if enc_codeword has no error

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

module br_ecc_secded_fpv_monitor #(
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

  localparam int EncLatency = 32'(EncRegisterInputs) + 32'(EncRegisterOutputs);
  localparam int DecLatency = 32'(DecRegisterInputs) + 32'(DecRegisterOutputs)
    + 32'(RegisterSyndrome);
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
