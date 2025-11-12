// SPDX-License-Identifier: Apache-2.0


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
// This module has parameterizable latency. By default, it is purely combinational,
// but it can have up to 2 cycles of delay (RegisterInputs and RegisterOutputs).
// The initiation interval is always 1 cycle.

`include "br_asserts_internal.svh"

module br_ecc_sed_decoder #(
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
    localparam int Latency = 32'(RegisterInputs) + 32'(RegisterOutputs)
) (
    // Positive edge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Decoder input (received codeword, possibly with errors)
    input logic                     rcv_valid,
    input logic [CodewordWidth-1:0] rcv_codeword,

    // Decoder output
    output logic dec_valid,
    output logic [CodewordWidth-1:0] dec_codeword,
    output logic dec_error_due,  // detected-but-uncorrectable error
    output logic dec_error_syndrome,
    output logic [DataWidth-1:0] dec_data
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
  logic rcv_valid_d;
  logic [CodewordWidth-1:0] rcv_codeword_d;

  br_delay_valid #(
      .Width(CodewordWidth),
      .NumStages(32'(RegisterInputs)),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_inputs (
      .clk,
      .rst,
      .in_valid(rcv_valid),
      .in(rcv_codeword),
      .out_valid(rcv_valid_d),
      .out(rcv_codeword_d),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  // ------
  // Compute syndrome
  // ------
  logic syndrome;
  logic due;

  // Even parity: the total number of 1s in a valid codeword
  // (including the parity bits) is even.
  //
  // (Also, in a linear code, syndrome 0 means a legal codeword.)
  assign syndrome = ^rcv_codeword_d;
  assign due = (syndrome != '0);

  //------
  // Optionally register the output signals.
  //------
  br_delay_valid #(
      .Width(CodewordWidth + 2),
      .NumStages(32'(RegisterOutputs)),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_delay_valid_outputs (
      .clk,
      .rst,
      .in_valid(rcv_valid_d),
      .in({rcv_codeword_d, syndrome, due}),
      .out_valid(dec_valid),
      .out({dec_codeword, dec_error_syndrome, dec_error_due}),
      .out_valid_stages(),  // unused
      .out_stages()  // unused
  );

  // SED code cannot correct errors, so just forward the message (data) portion
  // of the codeword as-is even if an error is detected.
  assign dec_data = dec_codeword[DataWidth-1:0];

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(latency_a, rcv_valid |-> ##Latency dec_valid)
  `BR_COVER_IMPL(due_c, dec_valid && dec_error_due)

endmodule : br_ecc_sed_decoder
