// SPDX-License-Identifier: Apache-2.0

module br_mux_bin_structured_gates_tb;

  parameter int NumSymbolsIn = 2;
  parameter int SymbolWidth = 8;
  localparam int SelectRange = 2 ** $clog2(NumSymbolsIn);

  logic clk;
  logic rst;

  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in;
  logic [SymbolWidth-1:0] out;
  logic out_valid;
  logic [$clog2(NumSymbolsIn)-1:0] select;

  br_mux_bin_structured_gates #(
      .NumSymbolsIn(NumSymbolsIn),
      .SymbolWidth (SymbolWidth)
  ) dut (
      .select,
      .in,
      .out,
      .out_valid
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    // Randomize the inputs
    for (int i = 0; i < NumSymbolsIn; i++) begin
      in[i] = $urandom_range(0, (2 ** SymbolWidth) - 1);
    end
    select = 0;
    td.reset_dut();

    // Check that the correct input is selected for each valid select value
    for (int i = 0; i < NumSymbolsIn; i++) begin
      select = i;
      td.wait_cycles();
      td.check_integer(out, in[i], $sformatf("Output does not match expected for select = %0d", i));
      td.check(out_valid, $sformatf("Output valid should be high for select = %0d", i));
    end

    // Check that out and out_valid are zero for out-of-range select values
    for (int i = NumSymbolsIn; i < SelectRange; i++) begin
      select = i;
      td.wait_cycles();
      td.check_integer(out, '0, $sformatf("Output should be zero for out-of-range select = %0d", i
                       ));
      td.check(!out_valid, $sformatf("Output valid should be low for out-of-range select = %0d", i
               ));
    end

    td.wait_cycles();
    td.finish();
  end

endmodule : br_mux_bin_structured_gates_tb
