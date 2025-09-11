// SPDX-License-Identifier: Apache-2.0

`include "br_asserts_internal.svh"

module br_arb_fixed_internal #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input  logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  `BR_ASSERT_STATIC(num_requesters_gte_2_A, NumRequesters >= 2)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign can_grant[0] = 1'b1;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  for (genvar i = 1; i < NumRequesters; i++) begin : gen_can_grant_upper
    assign can_grant[i] = !(|request[i-1:0]);
  end
  assign grant = request & can_grant;

endmodule : br_arb_fixed_internal
