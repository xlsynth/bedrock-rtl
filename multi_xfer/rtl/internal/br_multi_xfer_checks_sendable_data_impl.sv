// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Multi-Transfer Interface Checks (Implementation)
//
// This is an internal assertion-only module that can be reused in all
// modules with multi-transfer interfaces. It uses the Bedrock-internal
// implementation check macros to ensure the sendable and data signals
// conform to the multi-transfer interface protocol.

`include "br_asserts_internal.svh"
`include "br_registers.svh"
`include "br_unused.svh"

// ri lint_check_off NO_OUTPUT
module br_multi_xfer_checks_sendable_data_impl #(
    parameter int NumSymbols = 2,
    parameter int SymbolWidth = 1,
    parameter bit EnableAssertDataStability = 1,

    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    // ri lint_check_waive NOT_READ HIER_NET_NOT_READ INPUT_NOT_READ
    input logic clk,
    input logic rst,

    input logic [CountWidth-1:0] receivable,
    input logic [CountWidth-1:0] sendable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] data
);

  // If not all of the sendable symbols are transferred,
  // the remaining symbols must still be sendable and unchanged.
  `BR_ASSERT_IMPL(sendable_no_revocation_a, (sendable > receivable) |=> (sendable >= $past
                                            (sendable - receivable)))

`ifdef BR_ASSERT_ON
`ifdef BR_ENABLE_IMPL_CHECKS
  // Untransferred symbols shifted down to LS position
  logic [NumSymbols-1:0][SymbolWidth-1:0] data_shifted;
  // Mask newly arriving data to zero
  logic [NumSymbols-1:0][SymbolWidth-1:0] data_masked;
  logic [CountWidth-1:0] xfer_count;
  logic [CountWidth-1:0] hold_count, hold_count_d;

  assign xfer_count = (sendable < receivable) ? sendable : receivable;
  assign hold_count = (sendable > receivable) ? (sendable - receivable) : '0;

  `BR_REG(hold_count_d, hold_count)

  for (genvar i = 0; i < NumSymbols; i++) begin : gen_data_shifted
    // ri lint_check_waive VAR_INDEX_RANGE
    assign data_shifted[i] = (i < hold_count) ? data[i+xfer_count] : '0;
    assign data_masked[i]  = (i < hold_count_d) ? data[i] : '0;
  end
`endif
`endif
  if (EnableAssertDataStability) begin : gen_data_stability_checks
    for (genvar i = 0; i < NumSymbols; i++) begin : gen_data_known_checks
      // This isn't strictly needed for functionality, but if data is unknown,
      // the data_shifted_a assertion below will not work since unknown values
      // cannot be compared.
      `BR_ASSERT_IMPL(data_known_a, (sendable > i) |-> !$isunknown(data[i]))
    end
    `BR_ASSERT_IMPL(data_shifted_a, (sendable > receivable) |=> data_masked == $past(data_shifted))
  end else begin : gen_data_instability_cover
    `BR_COVER_IMPL(data_instability_c,
                   (sendable > receivable) ##1 data_masked != $past(data_shifted))
  end

  `BR_UNUSED_NAMED(all_unused, {rst, receivable, sendable, data})

endmodule
// ri lint_check_on NO_OUTPUT
