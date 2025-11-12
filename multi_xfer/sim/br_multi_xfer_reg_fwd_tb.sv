// SPDX-License-Identifier: Apache-2.0

module br_multi_xfer_reg_fwd_tb;
  parameter int NumSymbols = 2;
  parameter int SymbolWidth = 8;
  localparam int CountWidth = $clog2(NumSymbols + 1);

  logic clk;
  logic rst;

  logic [CountWidth-1:0] push_sendable;
  logic [CountWidth-1:0] push_receivable;
  logic [NumSymbols-1:0][SymbolWidth-1:0] push_data;

  logic [CountWidth-1:0] pop_sendable;
  logic [CountWidth-1:0] pop_receivable;
  logic [NumSymbols-1:0][SymbolWidth-1:0] pop_data;

  br_multi_xfer_reg_fwd #(
      .NumSymbols (NumSymbols),
      .SymbolWidth(SymbolWidth)
  ) dut (
      .clk,
      .rst,
      .push_sendable,
      .push_receivable,
      .push_data,
      .pop_sendable,
      .pop_receivable,
      .pop_data
  );

  br_test_driver td (
      .clk,
      .rst
  );

  initial begin
    logic [NumSymbols-1:0][SymbolWidth-1:0] expected_data;

    push_sendable = '0;
    push_data = '0;
    pop_receivable = '0;

    td.reset_dut();
    td.wait_cycles();

    td.check_integer(push_receivable, NumSymbols);

    // Send a single symbol.
    push_sendable = 1;
    for (int i = 0; i < NumSymbols; i++) begin
      push_data[i] = $urandom();
      expected_data[i] = push_data[i];
    end

    td.wait_cycles(1);

    // Check that the single symbol is buffered.
    // Don't pop it yet.
    push_sendable  = 0;
    pop_receivable = 0;

    td.check_integer(pop_sendable, 1);
    td.check_integer(pop_data[0], expected_data[0]);
    td.check_integer(push_receivable, NumSymbols - 1);

    td.wait_cycles(1);

    // The symbol should still be buffered.
    td.check_integer(pop_sendable, 1);
    td.check_integer(pop_data[0], expected_data[0]);

    // Pop the symbol now.
    pop_receivable = 1;
    td.wait_cycles(1);

    pop_receivable = 0;
    td.check_integer(pop_sendable, 0);

    // Send max number of symbols.
    push_sendable = NumSymbols;
    for (int i = 0; i < NumSymbols; i++) begin
      push_data[i] = $urandom();
      expected_data[i] = push_data[i];
    end

    td.wait_cycles(1);

    push_sendable = 0;

    // Check that the symbols are buffered.
    td.check_integer(push_receivable, 0);
    td.check_integer(pop_sendable, NumSymbols);
    for (int i = 0; i < NumSymbols; i++) begin
      td.check_integer(pop_data[i], expected_data[i]);
    end

    // Pop only one symbol.
    pop_receivable = 1;

    for (int i = 0; i < NumSymbols - 1; i++) begin
      expected_data[i] = expected_data[i+1];
    end

    td.wait_cycles(1);

    td.check_integer(pop_sendable, NumSymbols - 1);
    for (int i = 0; i < NumSymbols - 1; i++) begin
      td.check_integer(pop_data[i], expected_data[i]);
    end

    // Pop a symbol while sending two more.
    push_sendable  = 2;
    pop_receivable = 1;

    for (int i = 0; i < NumSymbols - 2; i++) begin
      expected_data[i] = expected_data[i+1];
    end

    for (int i = 0; i < 2; i++) begin
      push_data[i] = $urandom();
      expected_data[i+NumSymbols-2] = push_data[i];
    end

    td.wait_cycles(1);

    td.check_integer(pop_sendable, NumSymbols);
    for (int i = 0; i < NumSymbols; i++) begin
      td.check_integer(pop_data[i], expected_data[i]);
    end

    // Pop all symbols.
    pop_receivable = NumSymbols;
    push_sendable  = 0;
    td.wait_cycles(1);

    td.check_integer(pop_sendable, 0);

    td.finish();
  end

endmodule
