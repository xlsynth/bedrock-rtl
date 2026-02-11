// SPDX-License-Identifier: Apache-2.0

// Integration checks for the Superintelligent CSR Bus (SCB) protocol.
// Assertions only. No synthesisable logic in this module.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

// ri lint_check_off NO_OUTPUT
module br_csr_checks_intg #(
    // Must be at least 1
    parameter int AddrWidth = 1,
    // Must be either 32 or 64
    parameter int DataWidth = 32,
    // If 1, check that the address is in the range [AddrMin, AddrMax]
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableAddressRangeCheck = 0,
    // Must be at least 0 and at most AddrMax
    // ri lint_check_waive PARAM_NOT_USED
    parameter logic [AddrWidth-1:0] AddrMin = 0,
    // Must be at least AddrMin and less than (2 ** AddrWidth)
    // ri lint_check_waive PARAM_NOT_USED
    parameter logic [AddrWidth-1:0] AddrMax = 2 ** AddrWidth - 1,
    // If 1, check that each byte of the write data is known for a write
    // request if its strobe bit is set
    // ri lint_check_waive PARAM_NOT_USED
    parameter bit EnableWriteDataKnownCheck = 1,
    localparam int StrobeWidth = DataWidth / 8
) (
    // ri lint_check_waive INPUT_NOT_READ HIER_NET_NOT_READ HIER_BRANCH_NOT_READ
    input logic clk,
    input logic rst,

    input logic req_valid,
    input logic req_write,
    input logic [AddrWidth-1:0] req_addr,
    input logic [DataWidth-1:0] req_wdata,
    input logic [StrobeWidth-1:0] req_wstrb,
    input logic req_secure,
    input logic req_privileged,
    input logic req_abort,

    // Only the response valid signal is required to known when a request has completed
    input logic resp_valid
);
  `BR_ASSERT_STATIC(legal_addr_width_a, AddrWidth >= 1)
  `BR_ASSERT_STATIC(legal_data_width_a, DataWidth == 32 || DataWidth == 64)
  `BR_ASSERT_STATIC(legal_addr_min_a, AddrMin >= 0)
  `BR_ASSERT_STATIC(legal_addr_max_a, AddrMax <= (2 ** AddrWidth) - 1)
  `BR_ASSERT_STATIC(legal_range_a, AddrMin <= AddrMax)

`ifdef BR_ASSERT_ON
`ifndef BR_DISABLE_INTG_CHECKS

  logic set_inflight, clear_inflight;
  logic req_inflight, req_inflight_next;

  logic set_aborted, clear_aborted;
  logic req_aborted, req_aborted_next;

  // Set inflight on request, clear on response or abort
  assign set_inflight = req_valid;
  assign clear_inflight = resp_valid || req_abort;
  assign req_inflight_next = (req_inflight && !clear_inflight) || set_inflight;

  // We go into the aborted state if req_abort is set
  assign set_aborted = req_abort;
  // Clear the aborted state if the leaf responds or we get a new request
  assign clear_aborted = resp_valid || req_valid;
  assign req_aborted_next = (req_aborted && !clear_aborted) || set_aborted;

  `BR_REG(req_inflight, req_inflight_next)
  `BR_REG(req_aborted, req_aborted_next)

  `BR_ASSERT_INTG(no_request_when_inflight_a, req_valid |-> !req_inflight)
  `BR_ASSERT_INTG(only_abort_when_inflight_a, req_abort |-> req_inflight)
  `BR_ASSERT_INTG(no_abort_with_request_a, req_abort |-> !req_valid)
  `BR_ASSERT_INTG(response_only_when_inflight_or_aborted_a,
                  resp_valid |-> req_inflight || req_aborted)

  // Address, write, secure, and privileged must always be known for a request
  `BR_ASSERT_KNOWN_VALID_INTG(req_addr_known_a, req_valid, req_addr)
  `BR_ASSERT_KNOWN_VALID_INTG(req_write_known_a, req_valid, req_write)
  `BR_ASSERT_KNOWN_VALID_INTG(req_secure_known_a, req_valid, req_secure)
  `BR_ASSERT_KNOWN_VALID_INTG(req_privileged_known_a, req_valid, req_privileged)

  // Write strobe must always be known for a write request
  `BR_ASSERT_KNOWN_VALID_INTG(req_wstrb_known_a, req_valid && req_write, req_wstrb)
  if (EnableWriteDataKnownCheck) begin : gen_write_data_known_check
    for (genvar i = 0; i < StrobeWidth; i++) begin : gen_write_data_known_check_byte
      // The given byte of write-data must be known for a write request if its strobe bit is set
      `BR_ASSERT_KNOWN_VALID_INTG(req_wdata_known_a, req_valid && req_write && req_wstrb[i],
                                  req_wdata[i*8+:8])
    end
  end

  if (EnableAddressRangeCheck) begin : gen_range_check
    `BR_ASSERT_INTG(request_address_in_range_a, req_addr >= AddrMin && req_addr <= AddrMax)
  end

`endif
`endif

  // Mark all the signals unused to avoid lint warnings.
  `BR_UNUSED_NAMED(all_unused, {rst, req_valid, req_write, req_addr, req_wdata, req_wstrb,
                                req_secure, req_privileged, req_abort, resp_valid})

endmodule : br_csr_checks_intg
// ri lint_check_on NO_OUTPUT
