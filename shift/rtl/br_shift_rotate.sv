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
//
// Bedrock-RTL Barrel Rotate
//
// This module implements left/right rotation of a vector of symbols.
// It is purely combinational.
//
// The input vector is rotated left/right by the amount specified in the rotate input.
// For left rotation, the output is such that for every element i of the input,
//
// out[(i + rotate) % NumSymbols] == in[i]
//
// For right rotation, the output is such that for every element i of the input,
//
// out[i] == in[(i + rotate) % NumSymbols]
//
// The bits within each symbol are always rotated together.

`include "br_asserts_internal.svh"

module br_shift_rotate #(
    // Number of rotatable symbols in the input and output. Must be >=2.
    parameter  int NumSymbols  = 2,
    // The width of each symbol. Must be >=1.
    parameter  int SymbolWidth = 1,
    // The maximum number of symbols to rotate. Must be >=1.
    parameter  int MaxRotate   = (NumSymbols - 1),
    localparam int RotateWidth = $clog2(MaxRotate + 1)
) (
    // The vector to rotate.
    input logic [NumSymbols-1:0][SymbolWidth-1:0] in,
    // If 1, rotate right. If 0, rotate left.
    input logic right,
    // The amount to rotate by.
    input logic [RotateWidth-1:0] rotate,
    // The rotated vector.
    output logic [NumSymbols-1:0][SymbolWidth-1:0] out
);

  // Integration Checks

  `BR_ASSERT_STATIC(legal_num_symbols_a, NumSymbols >= 2)
  `BR_ASSERT_STATIC(legal_symbol_width_a, SymbolWidth >= 1)
  `BR_ASSERT_STATIC(legal_max_rotate_a, MaxRotate >= 1)

  // ri lint_check_waive ALWAYS_COMB
  `BR_ASSERT_COMB_INTG(rotate_in_range_a, rotate <= MaxRotate)

  // Implementation

  // The most you can actually rotate is NumSymbols - 1, anything larger
  // is equivalent to rotating by (rotate % NumSymbols).
  localparam int RealRotateWidth = $clog2(NumSymbols);
  localparam int ExtRotateWidth = $clog2(NumSymbols + 1);

  logic [RealRotateWidth-1:0] real_rotate;
  logic [ ExtRotateWidth-1:0] inv_rotate_ext;
  logic [RealRotateWidth-1:0] inv_rotate;
  logic [RealRotateWidth-1:0] left_rotate;

  if (MaxRotate > (NumSymbols - 1)) begin : gen_real_rotate_modulo
    // This is modulo by a constant, which shouldn't be that expensive.
    // TODO(zhemao): Figure out a way to efficiently implement this.
    // ri lint_check_waive MODULUS
    assign real_rotate = rotate % NumSymbols;
  end else begin : gen_real_rotate_no_modulo
    assign real_rotate = RealRotateWidth'(rotate);
  end

  // Right rotate of an N-entry vector by R is equivalent to left rotate of
  // the same vector by N-R. Make a special case for R == 0, since left
  // rotate by N is out-of-range. It is equivalent to rotate by 0.
  assign inv_rotate_ext = NumSymbols - real_rotate;
  assign inv_rotate = (real_rotate == 0) ? '0 : RealRotateWidth'(inv_rotate_ext);
  assign left_rotate = right ? inv_rotate : real_rotate;

  // Left rotation network
  // stages[0] is the input
  // stages[RealRotateWidth] is the output
  // stages[i+1] = stages[i] or stages[i] rotated left by 2^i
  // depending on left_rotate[i]
  logic [RealRotateWidth:0][NumSymbols-1:0][SymbolWidth-1:0] stages;

  assign stages[0] = in;
  assign out = stages[RealRotateWidth];

  for (genvar stage = 0; stage < RealRotateWidth; stage++) begin : gen_stages
    localparam int StageRotateAmount = 1 << stage;
    logic [NumSymbols-1:0][SymbolWidth-1:0] stage_in;
    logic [NumSymbols-1:0][SymbolWidth-1:0] stage_rot;

    assign stage_in = stages[stage];
    assign stage_rot = {
      stages[stage][NumSymbols-1-StageRotateAmount:0],
      stages[stage][NumSymbols-1:NumSymbols-StageRotateAmount]
    };
    assign stages[stage+1] = left_rotate[stage] ? stage_rot : stage_in;
  end

  // Implementation checks

  // TODO(zhemao): Decide what assertions we want to add here.

endmodule
