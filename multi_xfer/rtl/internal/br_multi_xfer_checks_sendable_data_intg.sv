// Copyright 2025 The Bedrock-RTL Authors
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

// Bedrock-RTL Multi-Transfer Interface Checks (Integration)
//
// This is an internal assertion-only module that can be reused in all
// modules with multi-transfer interfaces. It uses the Bedrock-internal
// integration check macros to ensure the sendable and data signals
// conform to the multi-transfer interface protocol.

`include "br_asserts_internal.svh"
`include "br_unused.svh"

// ri lint_check_off NO_OUTPUT
module br_multi_xfer_checks_sendable_data_intg #(
    parameter int NumSymbols  = 2,
    parameter int SymbolWidth = 1,

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
  `BR_ASSERT_INTG(sendable_no_revocation_a, (sendable > receivable) |=> (sendable >= $past
                                            (sendable - receivable)))

  for (genvar i = 0; i < NumSymbols; i++) begin : gen_sendable_data_qual
    // This isn't strictly needed for functionality, but if data is unknown,
    // the data_shifted_a assertion below will not work since unknown values
    // cannot be compared.
    `BR_ASSERT_INTG(data_known_a, (sendable > i) |-> !$isunknown(data[i]))
    `BR_ASSERT_INTG(data_shifted_a,
                    ((sendable > receivable) && ((sendable - receivable) > i))
        |=>
        (data[i] == $past(
                        data[i+receivable]
                    )))
  end

  `BR_UNUSED_NAMED(all_unused, {rst, receivable, sendable, data})

endmodule
// ri lint_check_on NO_OUTPUT
