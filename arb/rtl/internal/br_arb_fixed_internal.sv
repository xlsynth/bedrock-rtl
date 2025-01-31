// Copyright 2024-2025 The Bedrock-RTL Authors
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
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input  logic [NumRequesters-1:0] request,
    output logic [NumRequesters-1:0] can_grant,
    output logic [NumRequesters-1:0] grant
);

  //------------------------------------------
  // Implementation
  //------------------------------------------
  assign can_grant[0] = 1'b1;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
  for (genvar i = 1; i < NumRequesters; i++) begin : gen_can_grant_upper
    assign can_grant[i] = !(|request[i-1:0]);
  end
  assign grant = request & can_grant;

endmodule : br_arb_fixed_internal
