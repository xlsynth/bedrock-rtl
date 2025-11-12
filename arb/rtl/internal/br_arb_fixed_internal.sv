// SPDX-License-Identifier: Apache-2.0


// Bedrock-RTL Fixed-Priority Arbiter Internal Module
//
// Grants a single request at a time with fixed (strict) priority
// where the lowest index requester has the highest priority.
//
// This internal module exposes a 'can_grant' that is high if there are no
// requests of higher priority.  The final grant signal is equivalent to
// 'can_grant & request'.

`include "br_asserts_internal.svh"

module br_arb_fixed_internal #(
    // Must be at least 1
    parameter int NumRequesters = 1
) (
    input  logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  `BR_ASSERT_STATIC(num_requesters_gte_1_A, NumRequesters >= 1)

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign can_grant[0] = 1'b1;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  for (genvar i = 1; i < NumRequesters; i++) begin : gen_can_grant_upper
    assign can_grant[i] = !(|request[i-1:0]);
  end
  assign grant = request & can_grant;

endmodule : br_arb_fixed_internal
