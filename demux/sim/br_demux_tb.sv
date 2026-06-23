// SPDX-License-Identifier: Apache-2.0

//
// Bedrock-RTL-Eval One-Hot and Binary Select Demultiplexer Testbench

module br_demux_tb;

  parameter int NumSymbolsOut = 2;
  parameter int SymbolWidth = 8;
  parameter int DRAIN_TIME_CYCLES = 10;  // Time to observe all results in ns

  localparam int SelectWidth = br_math::clamped_clog2(NumSymbolsOut);

  logic clk;
  logic rst;

  logic [SelectWidth-1:0] bin_select;
  logic [NumSymbolsOut-1:0] onehot_select;
  logic in_valid;
  logic [SymbolWidth-1:0] in;

  logic [NumSymbolsOut-1:0] bin_out_valid;
  logic [NumSymbolsOut-1:0][SymbolWidth-1:0] bin_out;
  logic [NumSymbolsOut-1:0] onehot_out_valid;
  logic [NumSymbolsOut-1:0][SymbolWidth-1:0] onehot_out;

  br_demux_bin #(
      .NumSymbolsOut(NumSymbolsOut),
      .SymbolWidth(SymbolWidth),
      .EnableAssertFinalNotValid(1'b0)
  ) dut_bin (
      .select(bin_select),
      .in_valid,
      .in,
      .out_valid(bin_out_valid),
      .out(bin_out)
  );

  br_demux_onehot #(
      .NumSymbolsOut(NumSymbolsOut),
      .SymbolWidth(SymbolWidth),
      .EnableAssertFinalNotValid(1'b0)
  ) dut_onehot (
      .select(onehot_select),
      .in_valid,
      .in,
      .out_valid(onehot_out_valid),
      .out(onehot_out)
  );

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic check_replicated_data(input string test_name);
    for (int i = 0; i < NumSymbolsOut; i++) begin
      td.check(bin_out[i] === in, $sformatf("%s: bin out[%0d] data mismatch", test_name, i));
      td.check(onehot_out[i] === in, $sformatf("%s: onehot out[%0d] data mismatch", test_name, i));
    end
  endtask

  task automatic check_bin(input logic [NumSymbolsOut-1:0] expected_valid, input string test_name);
    td.check(bin_out_valid === expected_valid, $sformatf("%s: bin valid mismatch", test_name));
  endtask

  task automatic check_onehot(input logic [NumSymbolsOut-1:0] expected_valid,
                              input string test_name);
    td.check(onehot_out_valid === expected_valid, $sformatf("%s: onehot valid mismatch", test_name
             ));
  endtask

  initial begin
    logic [NumSymbolsOut-1:0] expected_valid;

    bin_select = '0;
    onehot_select = '0;
    in_valid = 1'b0;
    in = '0;

    td.reset_dut();
    td.wait_cycles(1);

    check_bin('0, "reset idle");
    check_onehot('0, "reset idle");
    check_replicated_data("reset idle");

    // Input data is invalid
    in = '1;
    in_valid = 1'b0;
    for (int select_idx = 0; select_idx < NumSymbolsOut; select_idx++) begin
      bin_select = select_idx[SelectWidth-1:0];
      onehot_select = '0;
      onehot_select[select_idx] = 1'b1;
      td.wait_cycles(1);
      check_bin('0, $sformatf("invalid bin select %0d", select_idx));
      check_onehot('0, $sformatf("invalid onehot select %0d", select_idx));
      check_replicated_data($sformatf("invalid select %0d", select_idx));
    end

    // Valid input data and test both demultiplexers
    in_valid = 1'b1;
    for (int select_idx = 0; select_idx < NumSymbolsOut; select_idx++) begin
      in = SymbolWidth'($urandom_range(0, (2 ** SymbolWidth) - 1));

      expected_valid = '0;
      expected_valid[select_idx] = 1'b1;

      bin_select = select_idx[SelectWidth-1:0];
      onehot_select = '0;
      onehot_select[select_idx] = 1'b1;
      td.wait_cycles(1);
      check_bin(expected_valid, $sformatf("valid bin select %0d", select_idx));
      check_onehot(expected_valid, $sformatf("valid onehot select %0d", select_idx));
      check_replicated_data($sformatf("valid select %0d", select_idx));
    end

    // Test only the binary select demultiplexer
    onehot_select = '0;
    in = '0;
    td.wait_cycles(1);
    check_onehot('0, "valid with no onehot select");
    check_replicated_data("valid with no onehot select");

    in_valid = 1'b0;
    td.wait_cycles(1);

    td.finish(DRAIN_TIME_CYCLES);
  end

endmodule : br_demux_tb
