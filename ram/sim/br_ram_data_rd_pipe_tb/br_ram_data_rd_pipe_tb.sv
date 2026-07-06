// SPDX-License-Identifier: Apache-2.0

module br_ram_data_rd_pipe_tb #(
    parameter int Width = 8,
    parameter int DepthTiles = 2,
    parameter int WidthTiles = 2,
    parameter int DepthStages = 1,
    parameter int WidthStages = 1,
    parameter int MaxTransactionsPerIteration = 64,
    localparam int Latency = DepthStages + WidthStages
);
  timeunit 1ns; timeprecision 1ps;

  import br_dv_lib::*;
  import br_ram_data_rd_pipe_tb_pkg::*;

  `include "br_dv_macros.svh"

  typedef br_ram_data_rd_pipe_env#(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) BrRamDataRdPipeEnv;

  initial begin
    string vcd_file;

    if ($value$plusargs("BR_VCD=%s", vcd_file)) begin
      $dumpfile(vcd_file);
      $dumpvars(0);
    end
  end

  localparam time TestTimeout = 100us;
  localparam int SequenceIterations = 7;
  localparam int IdleDataTransactions = 16;
  localparam int BubblePatternTransactions = 32;
  localparam int ContinuousStressTransactions = 128;
  localparam int PatternTransactions = (DepthTiles * WidthTiles * 4) + 8;
  localparam int WalkingOneTransactions = Width + 8;
  localparam int ResetPreValidTransactions = Latency + 2;
  localparam int ResetValidCycles = 2;
  localparam int DrainCycles = Latency + 4;
  localparam int MaxPatternTransactions = (WalkingOneTransactions > PatternTransactions) ?
      WalkingOneTransactions : PatternTransactions;
  localparam int MaxDirectedTransactions = (MaxPatternTransactions > ContinuousStressTransactions) ?
      MaxPatternTransactions : ContinuousStressTransactions;
  localparam int MaxSequenceTransactions = (MaxDirectedTransactions > MaxTransactionsPerIteration) ?
      MaxDirectedTransactions : MaxTransactionsPerIteration;
  localparam int SequenceTimeoutCycles = (MaxSequenceTransactions * 8) + 100;

  br_dv_clk_rst_if clk_rst_if ();
  br_ram_data_rd_pipe_input_if #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles)
  ) in_if ();
  br_ram_data_rd_pipe_output_if #(.Width(Width)) out_if ();

  br_ram_data_rd_pipe #(
      .Width(Width),
      .DepthTiles(DepthTiles),
      .WidthTiles(WidthTiles),
      .DepthStages(DepthStages),
      .WidthStages(WidthStages)
  ) dut (
      .clk(clk_rst_if.clk),
      .rst(clk_rst_if.rst),
      .tile_valid(in_if.tile_valid),
      .tile_data(in_if.tile_data),
      .valid(out_if.valid),
      .data(out_if.data)
  );

  `BR_DEFINE_TEST(br_ram_data_rd_pipe_test, TestTimeout)
  `BR_RUN_TEST(br_ram_data_rd_pipe_test)

  task automatic reset_on_next_valid(input BrRamDataRdPipeEnv env,
                                     input int unsigned valid_cycles_before_reset = 1);
    int unsigned valid_cycles;
    longint unsigned observed_cycle;
    longint unsigned reset_cycle;

    valid_cycles   = 0;
    observed_cycle = env.input_monitor.get_observed_cycle();
    while (valid_cycles < valid_cycles_before_reset) begin
      @(posedge clk_rst_if.clk);
      observed_cycle++;
      if (|in_if.tile_valid) begin
        valid_cycles++;
      end
    end
    reset_cycle = observed_cycle;
    clk_rst_if.rst = 1'b1;
    env.clk_rst_driver.wait_cycles();
    env.scoreboard.flush_inflight_expected_for_reset(reset_cycle);
    if (ResetValidCycles > 1) env.clk_rst_driver.wait_cycles(ResetValidCycles - 1);
    clk_rst_if.rst = 1'b0;
  endtask

  task automatic run_sequence_and_check(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    fork : sequence_run_fork
      env.input_sequence.start();
    join_none

    ctx.wait_for_sequences(env.clk_rst_driver, SequenceTimeoutCycles);
    disable sequence_run_fork;
    env.input_driver.drive_item(null);
    env.clk_rst_driver.wait_cycles(DrainCycles);
    env.scoreboard.check_all();
  endtask

  task automatic run_smoke_test(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(1, BrRamDataRdPipeValidActive);
    run_sequence_and_check(ctx, env);
  endtask

  task automatic run_idle_data_test(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(IdleDataTransactions, BrRamDataRdPipeValidIdle);
    run_sequence_and_check(ctx, env);
  endtask

  task automatic run_reset_valid_data_test(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(ResetPreValidTransactions, BrRamDataRdPipeValidActive,
                                   BrRamDataRdPipeDepthRoundRobin,
                                   BrRamDataRdPipePayloadWalkingOne);
    env.input_sequence.fill_random(ResetValidCycles + 1, BrRamDataRdPipeValidActive,
                                   BrRamDataRdPipeDepthRoundRobin,
                                   BrRamDataRdPipePayloadWalkingOne);
    env.input_sequence.fill_random(ResetValidCycles + 1, BrRamDataRdPipeValidIdle);
    env.input_sequence.fill_random(ContinuousStressTransactions, BrRamDataRdPipeValidActive);
    fork : reset_on_valid_fork
      reset_on_next_valid(env, ResetPreValidTransactions);
    join_none
    run_sequence_and_check(ctx, env);
    disable reset_on_valid_fork;
  endtask

  task automatic run_bubble_pattern_test(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(BubblePatternTransactions, BrRamDataRdPipeValidBubblePattern,
                                   BrRamDataRdPipeDepthRoundRobin,
                                   BrRamDataRdPipePayloadWalkingOne);
    run_sequence_and_check(ctx, env);
  endtask

  task automatic run_continuous_stress_test(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(ContinuousStressTransactions, BrRamDataRdPipeValidActive);
    run_sequence_and_check(ctx, env);
  endtask

  task automatic run_pattern_tests(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    env.input_sequence.fill_random(PatternTransactions, BrRamDataRdPipeValidActive,
                                   BrRamDataRdPipeDepthRoundRobin,
                                   BrRamDataRdPipePayloadTilePattern);
    run_sequence_and_check(ctx, env);

    env.input_sequence.fill_random(WalkingOneTransactions, BrRamDataRdPipeValidActive,
                                   BrRamDataRdPipeDepthRoundRobin,
                                   BrRamDataRdPipePayloadWalkingOne);
    run_sequence_and_check(ctx, env);
  endtask

  task automatic run_random_tests(input br_dv_context ctx, input BrRamDataRdPipeEnv env);
    for (int i = 0; i < SequenceIterations; i++) begin
      env.input_sequence.fill_random($urandom_range(1, MaxTransactionsPerIteration));
      run_sequence_and_check(ctx, env);
    end
  endtask

  task automatic run_all_tests();
    begin
      br_dv_context ctx;
      BrRamDataRdPipeEnv env;

      ctx = new(test);
      ctx.check(MaxTransactionsPerIteration > 0, "MaxTransactionsPerIteration must be positive");
      ctx.check(ResetValidCycles > 0, "ResetValidCycles must be positive");

      env = new(ctx, clk_rst_if, in_if, out_if, Latency);

      env.clk_rst_driver.reset_dut();
      env.clk_rst_driver.wait_cycles();

      run_smoke_test(ctx, env);
      run_idle_data_test(ctx, env);
      run_reset_valid_data_test(ctx, env);
      run_bubble_pattern_test(ctx, env);
      run_continuous_stress_test(ctx, env);
      run_pattern_tests(ctx, env);
      run_random_tests(ctx, env);
    end
  endtask
endmodule : br_ram_data_rd_pipe_tb
