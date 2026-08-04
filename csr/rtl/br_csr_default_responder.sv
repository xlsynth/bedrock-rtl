// SPDX-License-Identifier: Apache-2.0
//
// Bedrock-RTL CSR Default Responder
//
// Return a registered decode-error response for every SCB request. The request
// payload and abort signal do not affect the response.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

module br_csr_default_responder #(
    parameter int AddrWidth = 1,  // Must be at least 1
    parameter int DataWidth = 32,  // Must be either 32 or 64
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic req_valid,
    input logic req_write,
    input logic [AddrWidth-1:0] req_addr,
    input logic [DataWidth-1:0] req_wdata,
    input logic [StrobeWidth-1:0] req_wstrb,
    input logic req_privileged,
    input logic req_secure,
    input logic req_abort,

    output logic resp_valid,
    output logic [DataWidth-1:0] resp_rdata,
    output logic resp_slverr,
    output logic resp_decerr
);
  // Integration checks
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth == 32 || DataWidth == 64)

  br_csr_checks_intg #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .EnableWriteDataKnownCheck(0)
  ) br_csr_checks_intg_inst (
      .clk,
      .rst,
      .req_valid,
      .req_write,
      .req_addr,
      .req_wdata,
      .req_wstrb,
      .req_secure,
      .req_privileged,
      .req_abort,
      .resp_valid
  );

  // Implementation
  `BR_REG(resp_valid, req_valid)

  assign resp_rdata  = '0;
  assign resp_slverr = 1'b0;
  assign resp_decerr = resp_valid;

  `BR_UNUSED_NAMED(unused_request, {req_write, req_addr, req_wdata, req_wstrb, req_privileged,
                                    req_secure, req_abort})

  // Implementation checks
  `BR_ASSERT_IMPL(request_produces_response_a, req_valid |=> resp_valid)
  `BR_ASSERT_IMPL(idle_produces_no_response_a, !req_valid |=> !resp_valid)
  `BR_ASSERT_IMPL(response_is_decode_error_a,
                  resp_valid |-> resp_decerr && !resp_slverr && resp_rdata == '0)

endmodule : br_csr_default_responder
