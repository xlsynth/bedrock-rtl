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

// Core FIFO push control logic that will be reused across different variants.
// Contains just the bypass and RAM write logic, leaving occupancy tracking up to
// the instantiating module.

`include "br_unused.svh"

module br_fifo_push_ctrl_core #(
    parameter int Depth = 2,
    parameter int Width = 1,
    parameter bit EnableBypass = 1,
    localparam int AddrWidth = $clog2(Depth)
) (
    // Posedge-triggered clock.
    input logic clk,
    // Synchronous active-high reset.
    input logic rst,

    // Push-side interface.
    output logic             push_ready,
    input  logic             push_valid,
    input  logic [Width-1:0] push_data,

    // Bypass interface
    // Bypass is only used when EnableBypass is 1, hence lint waiver.
    input  logic             bypass_ready,           // ri lint_check_waive INEFFECTIVE_NET
    output logic             bypass_valid_unstable,
    output logic [Width-1:0] bypass_data_unstable,

    // RAM interface
    output logic                 ram_wr_valid,
    output logic [AddrWidth-1:0] ram_wr_addr,
    output logic [    Width-1:0] ram_wr_data,

    // Signals to/from internal logic
    input  logic full,
    output logic push_beat
);

  //------------------------------------------
  // Implementation
  //------------------------------------------

  // Flow control
  assign push_beat  = push_ready && push_valid;
  assign push_ready = !full;

  // RAM path
  br_counter_incr #(
      .MaxValue(Depth - 1),
      .MaxIncrement(1)
  ) br_counter_incr_wr_addr (
      .clk,
      .rst,
      .reinit(1'b0),  // unused
      .initial_value(AddrWidth'(1'b0)),
      .incr_valid(ram_wr_valid),
      .incr(1'b1),
      .value(ram_wr_addr),
      .value_next()  // unused
  );

  // Datapath
  if (EnableBypass) begin : gen_bypass
    assign bypass_valid_unstable = push_valid;
    assign bypass_data_unstable = push_data;

    assign ram_wr_valid = push_beat && !bypass_ready;
    assign ram_wr_data = push_data;
  end else begin : gen_no_bypass
    `BR_UNUSED(bypass_ready)
    // TODO(zhemao, #157): Replace this with BR_TIEOFF macros once they are fixed
    assign bypass_valid_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT
    assign bypass_data_unstable = '0;  // ri lint_check_waive CONST_ASSIGN CONST_OUTPUT

    assign ram_wr_valid = push_beat;
    assign ram_wr_data = push_data;
  end

endmodule
