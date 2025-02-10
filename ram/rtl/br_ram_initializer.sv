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

// Bedrock-RTL RAM Initializer
//
// After exiting reset, initializes a RAM by writing each entry
// with a given initial value. Indicates when initialization has completed.

`include "br_registers.svh"
`include "br_asserts_internal.svh"

module br_ram_initializer #(
    parameter int Depth = 2,  // Number of entries in the RAM. Must be at least 2.
    parameter int Width = 1,  // Width of each entry in the RAM. Must be at least 1.
    localparam int AddressWidth = $clog2(Depth)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,
    // The value to write into each entry of the RAM.
    input logic [Width-1:0] initial_value,
    // Starts the initialization process. The first write occurs on the next clock cycle.
    input logic start,
    // Busy is asserted while initialization is in progress.
    // While busy, the user is responsible for ensuring that:
    // 1) the RAM write-port is exclusively driven by the br_ram_initializer
    // 2) there are no write address conflicts with any other write ports
    // 3) the initial_value is stable
    output logic busy,
    // RAM write-port interface.
    output logic wr_valid,
    output logic [AddressWidth-1:0] wr_addr,
    output logic [Width-1:0] wr_data
);

  //------------------------------------------
  // Integration checks
  //------------------------------------------
  `BR_ASSERT_STATIC(depth_gte_2_a, Depth >= 2)
  `BR_ASSERT_STATIC(width_gte_1_a, Width >= 1)

  `BR_ASSERT_INTG(initial_value_stable_when_busy_a, busy |-> $stable(initial_value))

  //------------------------------------------
  // Implementation
  //------------------------------------------
  typedef enum logic {
    Idle = 1'b0,
    Busy = 1'b1
  } state_t;

  state_t state, state_next;
  logic [AddressWidth-1:0] wr_addr_next, wr_addr_final;

  `BR_REGI(state, state_next, Idle)
  `BR_REGL(wr_addr, wr_addr_next, wr_valid)

  assign wr_valid = state == Busy;
  assign wr_data = initial_value;
  assign wr_addr_next = wr_addr + 1'b1;
  assign wr_addr_final = Depth - 1;
  assign busy = state == Busy;

  always_comb begin
    unique case (state)
      Idle: state_next = start ? Busy : Idle;
      Busy: state_next = wr_addr == wr_addr_final ? Idle : Busy;
      default: state_next = state_t'(1'bx);  // fully specified case statement (do x-prop)
    endcase
  end

  //------------------------------------------
  // Implementation checks
  //------------------------------------------
  `BR_ASSERT_IMPL(wr_addr_in_range_a, wr_addr < Depth)
  `BR_ASSERT_FINAL(final_not_busy_a, !busy)

endmodule : br_ram_initializer
