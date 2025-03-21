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
// Bedrock-RTL Barrel Rotate Testbench

module br_shift_rotate_tb;
  parameter int NumSymbols = 2;
  parameter int SymbolWidth = 1;
  parameter int MaxRotate = NumSymbols - 1;
  localparam int RotateWidth = $clog2(MaxRotate + 1);

  logic clk;
  logic rst;

  logic [NumSymbols-1:0][SymbolWidth-1:0] in;
  logic right;
  logic [RotateWidth-1:0] rotate;
  logic [NumSymbols-1:0][SymbolWidth-1:0] out;
  logic [NumSymbols-1:0][SymbolWidth-1:0] expected_out;

  br_shift_rotate #(
      .NumSymbols (NumSymbols),
      .SymbolWidth(SymbolWidth),
      .MaxRotate  (MaxRotate)
  ) dut (
      .in,
      .right,
      .rotate,
      .out
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    in <= '0;
    rotate <= '0;

    @(posedge clk);

    for (int i = 0; i < NumSymbols; i++) begin
      in[i] = $urandom_range(0, 2 ** SymbolWidth - 1);
    end

    // Test left rotation
    right <= 0;
    for (int i = 0; i < MaxRotate; i++) begin
      foreach (in[j]) begin
        expected_out[(j+i)%NumSymbols] = in[j];
      end

      rotate <= i;
      @(posedge clk);

      foreach (out[j]) begin
        td.check_integer(out[j], expected_out[j], $sformatf(
                         "left rotate by %0d: out[%0d] does not match expected[%0d]", i, j, j));
      end
    end

    // Test right rotation
    right <= 1;
    for (int i = 0; i < MaxRotate; i++) begin
      foreach (expected_out[j]) begin
        expected_out[j] = in[(j+i)%NumSymbols];
      end

      rotate <= i;
      @(posedge clk);

      foreach (out[j]) begin
        td.check_integer(out[j], expected_out[j], $sformatf(
                         "right rotate by %0d: out[%0d] does not match expected[%0d]", i, j, j));
      end
    end

    td.finish();
  end
endmodule
