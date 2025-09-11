// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_ecc_sed_encoder #(
    parameter int DataWidth = 1,  // Must be at least 1
    // If 1, then insert a pipeline register at the input.
    parameter bit RegisterInputs = 0,
    // If 1, then insert a pipeline register at the output.
    parameter bit RegisterOutputs = 0,
    // If 1, then assert there are no valid bits asserted at the end of the test.
    parameter bit EnableAssertFinalNotValid = 1,
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
      .NumStages(RegisterOutputs == 1 ? 1 : 0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
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
  `BR_ASSERT_FINAL(final_not_enc_valid_a, !enc_valid)

endmodule : br_ecc_sed_encoder
