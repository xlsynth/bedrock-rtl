module br_mux_onehot_tb;

  parameter int NumSymbolsIn = 2;
  localparam int SymbolWidth = 8;
  localparam bit EnableAssertSelectOnehot = 0;

  logic clk;
  logic rst;

  logic [NumSymbolsIn-1:0] select;
  logic [NumSymbolsIn-1:0][SymbolWidth-1:0] in;
  logic [SymbolWidth-1:0] out;

  br_mux_onehot #(
      .NumSymbolsIn(NumSymbolsIn),
      .SymbolWidth(SymbolWidth),
      .EnableAssertSelectOnehot(EnableAssertSelectOnehot)
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
    select = '0;
    for (int i = 0; i < NumSymbolsIn; i++) begin
      in[i] = i + 1;
    end

    td.reset_dut();
    td.wait_cycles(1);

    td.check_integer(out, 8'h00, "check no select");

    for (int i = 0; i < NumSymbolsIn; i++) begin
      select = '0;
      select[i] = 1'b1;
      td.wait_cycles(1);
      td.check_integer(out, i + 1, $sformatf("check select %d", i));
    end

    select = '1;
    td.wait_cycles(1);
    td.check($isunknown(out), "check select invalid");

    td.wait_cycles(1);

    td.finish();
  end
endmodule
