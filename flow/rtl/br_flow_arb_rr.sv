// Copyright 2024 The Bedrock-RTL Authors
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

// Bedrock-RTL Flow-Controlled Arbiter (Round-Robin)
//
// Grants a single request at a time with round-robin priority
// where the lowest index requester initializes with the highest priority.
// Uses ready-valid flow control for requesters (push)
// and the grant (pop).
//
// 0-cycle latency, but clock and reset are still needed to manage
// the internal arbiter priority state.
//
// TODO(mgottscho): Write spec

`include "br_registers.sv"
`include "br_asserts_internal.sv"

module br_flow_arb_rr #(
    // Must be at least 2
    parameter int NumRequesters = 2
) (
    input logic clk,
    input logic rst,
    output logic [NumRequesters-1:0] push_ready,
    input logic [NumRequesters-1:0] push_valid,
    input logic pop_ready,
    output logic pop_valid
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  // Rely on submodule integration checks

  // TODO(mgottscho): Add more

  //------------------------------------------
  // Implementation
  //------------------------------------------
  logic enable = |pop_ready;

  br_arb_rr #(
      .NumRequesters(NumRequesters)
  ) br_arb_rr (
      .clk,
      .rst,
      .enable,
      .request(push_valid),
      .grant
  );

  assign pop_valid = |push_valid;

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  // Rely on submodule implementation checks

  // TODO(mgottscho): Add more

endmodule : br_flow_arb_rr
