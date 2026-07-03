// SPDX-License-Identifier: Apache-2.0

module br_ram_addr_decoder_tb #(
    parameter int Depth = 32,
    parameter int DataWidth = 8,
    parameter int Tiles = 4,
    parameter int Stages = 1,
    parameter bit EnableDatapath = 1,
    parameter int MaxTransactionsPerIteration = 43,
    localparam int TileDepth = br_math::ceil_div(Depth, Tiles),
    localparam int InputAddressWidth = br_math::clamped_clog2(Depth),
    localparam int OutputAddressWidth = br_math::clamped_clog2(TileDepth)
);
  timeunit 1ns; timeprecision 1ps;

  import br_dv_lib::*;
  import br_ram_addr_decoder_tb_pkg::*;

  `include "br_dv_lib/br_dv_macros.svh"

  initial begin
    string vcd_file;

    if ($value$plusargs("BR_VCD=%s", vcd_file)) begin
      $dumpfile(vcd_file);
      $dumpvars(0);
    end
  end

  localparam time TestTimeout = 100us;
  localparam int SequenceIterations = 7;
  localparam int DrainCycles = Stages + 4;
  localparam int SequenceTimeoutCycles = (MaxTransactionsPerIteration * 8) + 100;

  br_dv_clk_rst_if clk_rst_if ();
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(InputAddressWidth)
  ) in_addr_if ();
  br_ram_addr_decoder_if #(
      .Tiles(1),
      .Width(DataWidth)
  ) in_data_if ();
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(OutputAddressWidth)
  ) out_addr_if ();
  br_ram_addr_decoder_if #(
      .Tiles(Tiles),
      .Width(DataWidth)
  ) out_data_if ();

  br_ram_addr_decoder #(
      .Depth(Depth),
      .DataWidth(DataWidth),
      .Tiles(Tiles),
      .Stages(Stages),
      .EnableDatapath(EnableDatapath)
  ) dut (
      .clk(clk_rst_if.clk),
      .rst(clk_rst_if.rst),
      .in_valid(in_addr_if.valid[0]),
      .in_addr(in_addr_if.data[0]),
      .in_data_valid(in_data_if.valid[0]),
      .in_data(in_data_if.data[0]),
      .out_valid(out_addr_if.valid),
      .out_addr(out_addr_if.data),
      .out_data_valid(out_data_if.valid),
      .out_data(out_data_if.data)
  );

  task automatic run_all_tests();
    begin
      br_dv_context ctx;
      br_ram_addr_decoder_env #(
          .InputAddressWidth(InputAddressWidth),
          .DataWidth(DataWidth),
          .Tiles(Tiles),
          .OutputAddressWidth(OutputAddressWidth),
          .MaxAddressValue(Depth - 1)
      ) env;
      int unsigned transactions;

      ctx = new(test);
      ctx.check(InputAddressWidth <= 64,
                "InputAddressWidth must fit br_ram_addr_decoder_item.data");
      ctx.check(DataWidth <= 64, "DataWidth must fit br_ram_addr_decoder_item.data");
      ctx.check(MaxTransactionsPerIteration > 0, "MaxTransactionsPerIteration must be positive");

      env =
          new(ctx, clk_rst_if, in_addr_if, in_data_if, out_addr_if, out_data_if, TileDepth, Stages);

      env.clk_rst_driver.reset_dut();
      env.clk_rst_driver.wait_cycles();

      for (int i = 0; i < SequenceIterations; i++) begin
        transactions = $urandom_range(1, MaxTransactionsPerIteration);
        env.input_sequence.fill_random(transactions, EnableDatapath);

        fork
          env.input_sequence.start();
        join_none

        ctx.wait_for_sequences(env.clk_rst_driver, SequenceTimeoutCycles);
        env.clk_rst_driver.wait_cycles(DrainCycles);
      end

      env.scoreboard.check_all();
    end
  endtask

  `BR_DEFINE_TEST(br_ram_addr_decoder_test, TestTimeout)
  `BR_RUN_TEST(br_ram_addr_decoder_test)
endmodule : br_ram_addr_decoder_tb
