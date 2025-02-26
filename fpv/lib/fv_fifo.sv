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

`include "br_asserts.svh"

module fv_fifo #(
    parameter int Depth = 4,
    parameter int DataWidth = 4,
    parameter int Bypass = 0
) (
    input logic clk,
    input logic rst,
    input logic push,
    input logic [DataWidth-1:0] push_data,
    input logic pop,
    output logic [DataWidth-1:0] pop_data,
    output logic empty,
    output logic full
);

  localparam int Width = $clog2(Depth);
  logic [Width:0] counter;
  logic [Width-1:0] rd_ptr, wr_ptr;
  logic [Depth-1:0][DataWidth-1:0] mem;
  logic wr_incr, rd_incr;

  assign empty = counter == 0;
  assign full  = counter == Depth;

  if (Bypass) begin : gen_bypass
    assign pop_data = empty ? push_data : mem[rd_ptr];
    assign wr_incr  = !empty ? push : push & !pop;
    assign rd_incr  = !empty ? pop : pop & !push;
  end else begin : gen_normal
    assign pop_data = mem[rd_ptr];
    assign wr_incr  = push;
    assign rd_incr  = pop;
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      counter <= 'd0;
      wr_ptr  <= 'd0;
      rd_ptr  <= 'd0;
    end else begin
      counter <= counter + push - pop;
      wr_ptr  <= wr_incr ? (wr_ptr == (Depth - 1) ? 'd0 : wr_ptr + 'd1) : wr_ptr;
      rd_ptr  <= rd_incr ? (rd_ptr == (Depth - 1) ? 'd0 : rd_ptr + 'd1) : rd_ptr;
      if (push) begin
        mem[wr_ptr] <= push_data;
      end
    end
  end

  if (Bypass) begin : gen_Bypass_ast
    `BR_ASSERT(no_push_full_a, full & !pop |-> !push)
    `BR_ASSERT(no_pop_empty_a, empty & !push |-> !pop)
  end else begin : gen_ast
    `BR_ASSERT(no_push_full_a, full |-> !push)
    `BR_ASSERT(no_pop_empty_a, empty |-> !pop)
  end

endmodule
