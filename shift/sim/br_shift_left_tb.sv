// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL Barrel Right Shift Testbench

module br_shift_left_tb;
  parameter int NumSymbols = 2;
  parameter int SymbolWidth = 1;
  localparam int MaxShift = NumSymbols - 1;
  localparam int ShiftWidth = $clog2(MaxShift + 1);

  logic clk;
  logic rst;

  logic [NumSymbols-1:0][SymbolWidth-1:0] in;
  logic [ShiftWidth-1:0] shift;
  logic [SymbolWidth-1:0] fill;
  logic [NumSymbols-1:0][SymbolWidth-1:0] out;
  logic [NumSymbols-1:0][SymbolWidth-1:0] expected_out;

  br_shift_left #(
      .NumSymbols (NumSymbols),
      .SymbolWidth(SymbolWidth),
      .MaxShift   (MaxShift)
  ) dut (
      .in,
      .shift,
      .fill,
      .out,
      .out_valid()  // unused
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    td.reset_dut();

    @(negedge clk);
    in = '0;
    shift = '0;
    fill = '0;

    for (int i = 0; i < NumSymbols; i++) begin
      in[i] = $urandom_range(0, 2 ** SymbolWidth - 1);
    end

    fill = $urandom_range(0, 2 ** SymbolWidth - 1);

    // Test left shift

    for (int i = 0; i < MaxShift; i++) begin
      @(negedge clk);

      for (int j = 0; j < (NumSymbols - i); j++) begin
        expected_out[j+i] = in[j];
      end

      for (int j = 0; j < i; j++) begin
        expected_out[j] = fill;
      end

      shift = i;
      @(posedge clk);

      foreach (out[j]) begin
        td.check_integer(out[j], expected_out[j], $sformatf(
                         "left shift by %0d: out[%0d] does not match expected[%0d]", i, j, j));
      end
    end

    td.finish();
  end
endmodule
