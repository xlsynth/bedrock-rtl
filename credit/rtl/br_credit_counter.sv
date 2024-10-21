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

// Bedrock-RTL Credit Counter
//
// Tracks a pool of credits used for long-distance flow control.
// It can be instantiated on either the sender or receiver side.
// For example, the sender side behavior is to increment when a
// a credit is replenished from the receiver, and decrement when
// a flit it sent; the receiver side behavior is to increment
// when a flit is received and decrement when returning a credit to
// the sender.
//
// The counter supports parameterized increments and decrements, with
// MaxChange defining the maximum inclusive change amount (default is 1).
// The maximum inclusive credit counter value is defined by MaxValue (default
// is 1). The counter can increment and decrement on the same cycle, potentially
// by different amounts.
//
// The user is responsible for ensuring the credit counter never overflows or
// underflows. This is checked by assertions.
//
// The actual data (flits) do not flow through this module.
//
// Resets to initial_value, which is a port rather than a parameter to accommodate
// designs where the initial value needs to be adjustable.

`include "br_asserts_internal.svh"
`include "br_registers.svh"

module br_credit_counter #(
    parameter int MaxValue = 1,  // Maximum credit counter value (inclusive). Default is 1.
    parameter int MaxChange = 1,  // Maximum increment/decrement amount (inclusive). Default is 1.
    localparam int ValueWidth = $clog2(MaxValue + 1),
    localparam int ChangeWidth = $clog2(MaxChange + 1)
) (
    // Posedge-triggered clock.
    input  logic                   clk,
    // Synchronous active-high reset.
    input  logic                   rst,
    input  logic [ ValueWidth-1:0] initial_value,
    input  logic                   incr_valid,
    input  logic [ChangeWidth-1:0] incr,
    input  logic                   decr_valid,
    input  logic [ChangeWidth-1:0] decr,
    output logic [ ValueWidth-1:0] value,
    output logic [ ValueWidth-1:0] value_next
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------

  //------------------------------------------
  // Implementation
  //------------------------------------------

  //------------------------------------------
  // Implementation checks
  //------------------------------------------

endmodule : br_credit_counter
