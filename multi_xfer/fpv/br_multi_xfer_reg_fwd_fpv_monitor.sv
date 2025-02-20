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

// Bedrock-RTL Multi-Transfer Register (Forward Variant)

`include "br_asserts.svh"
`include "br_registers.svh"

module br_multi_xfer_reg_fwd_fpv_monitor #(
    // The number of symbols that can be transferred in a single cycle.
    // Must be at least 2.
    parameter int NumSymbols = 2,
    // The width of a single symbol.
    // Must be at least 1.
    parameter int SymbolWidth = 1,
    // If 1, assert that the buffer is empty and push_sendable is 0
    // at end of simulation.
    parameter int EnableAssertFinalNotSendable = 1,

    localparam int CountWidth = $clog2(NumSymbols + 1)
) (
    input logic clk,
    input logic rst,

    input logic [CountWidth-1:0] push_receivable,
    input logic [CountWidth-1:0] push_sendable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] push_data,

    input logic [CountWidth-1:0] pop_receivable,
    input logic [CountWidth-1:0] pop_sendable,
    input logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data
);

  // ----------FV modeling code----------
  logic push_extra_left;
  logic pop_extra_left;
  logic [CountWidth-1:0] fv_pushed;
  logic [CountWidth-1:0] fv_popped;
  logic [NumSymbols-1:0] fv_push_valid;
  logic [NumSymbols-1:0] fv_pop_valid;
  logic [CountWidth-1:0] fv_pop_sendable;
  logic [CountWidth-1:0] fv_push_receivable, fv_push_receivable_pre;

  assign push_extra_left = push_sendable > push_receivable;
  assign pop_extra_left = pop_sendable > pop_receivable;
  assign fv_pushed = push_extra_left ? push_receivable : push_sendable;
  assign fv_popped = pop_extra_left ? pop_receivable : pop_sendable;

  // if fv_push_valid[i]=1, push_data[i] is actually pushed this cycle
  always_comb begin
    fv_push_valid = 'd0;
    for (int i = 0; i < NumSymbols; i++) begin
        if (i < fv_pushed) begin
            fv_push_valid[i] = 1'd1;
        end
    end
  end

  // if fv_pop_valid[i]=1, pop_data[i] is actually popped this cycle
  always_comb begin
    fv_pop_valid = 'd0;
    for (int i = 0; i < NumSymbols; i++) begin
        if (i < fv_popped) begin
            fv_pop_valid[i] = 1'd1;
        end
    end
  end

  `BR_REG(fv_pop_sendable, fv_pop_sendable + fv_pushed - fv_popped)
  `BR_REGI(fv_push_receivable_pre, fv_push_receivable_pre - fv_pushed + fv_popped, NumSymbols)
  // same cycle popped symbols are reflected in push_receivable
  assign fv_push_receivable = fv_push_receivable_pre + fv_popped;

  // ----------FV assumptions----------
  `BR_ASSUME(push_receivable_range_a, push_sendable <= NumSymbols)
  `BR_ASSUME(pop_receivable_range_a, pop_receivable <= NumSymbols)
  `BR_ASSUME(push_receivable_increment_a,
             push_extra_left |=> push_sendable >= $past(push_sendable - push_receivable))
  for (genvar i = 0; i < NumSymbols; i++) begin : gen_asm
    `BR_ASSUME(push_data_shift_down_a,
               push_extra_left |=> push_data[i] == $past(push_data[i+push_receivable]))
  end

  // ----------FV assertions----------
  `BR_ASSERT(pop_sendable_a, pop_sendable == fv_pop_sendable)
  `BR_ASSERT(push_receivable_a, push_receivable == fv_push_receivable)

  // ----------Data integrity Check----------
  // push side will only push actual pushed data
  // pop side will check actual popped data
  jasper_scoreboard_3 #(
      .CHUNK_WIDTH(SymbolWidth),
      .IN_CHUNKS(NumSymbols),
      .OUT_CHUNKS(NumSymbols),
      .SINGLE_CLOCK(1),
      .MAX_PENDING(NumSymbols)
  ) scoreboard (
      .clk(clk),
      .rstN(!rst),
      .incoming_vld(fv_push_valid),
      .incoming_data(push_data),
      .outgoing_vld(fv_pop_valid),
      .outgoing_data(pop_data)
  );

endmodule : br_multi_xfer_reg_fwd_fpv_monitor

bind br_multi_xfer_reg_fwd br_multi_xfer_reg_fwd_fpv_monitor #(
    .NumSymbols(NumSymbols),
    .SymbolWidth(SymbolWidth),
    .EnableAssertFinalNotSendable(EnableAssertFinalNotSendable)
) monitor (.*);
