module br_mux_bin_tb;

  localparam int NumSymbolsIn = 2;
  localparam int SymbolWidth = 8;
  localparam bit UseStructuredGates = 0;

  logic clk;
  logic rst;

  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in;
  logic [SymbolWidth-1:0] out;
  logic [$clog2(NumSymbolsIn)-1:0] select;

  br_mux_bin #(
      .NumSymbolsIn(NumSymbolsIn),
      .SymbolWidth(SymbolWidth),
      .UseStructuredGates(UseStructuredGates)
  ) dut (
      .select,
      .in,
      .out
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

    // Check that the correct input is selected for each possible select value
    for (int i = 0; i < NumSymbolsIn; i++) begin
      select = i;
      td.wait_cycles();
      td.check_integer(out, in[i], $sformatf("Output does not match expected for select = %0d", i));
    end

    td.wait_cycles();
    td.finish();
  end

endmodule : br_mux_bin_tb