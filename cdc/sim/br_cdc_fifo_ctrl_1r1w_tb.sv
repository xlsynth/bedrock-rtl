// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Directed simulation testbench for br_cdc_fifo_ctrl_1r1w.
 *
 * Scope:
 * - Reset and idle status checks in both clock domains.
 * - Directed push/pop, full/backpressure, and pop-stall behavior.
 * - Payload ordering checks for every accepted pop.
 * - External 1R1W RAM timing through br_ram_flops.
 * - Bazel-swept depth, width, RAM latency, pop-output registration, CDC
 *   synchronizer depth, and push/pop clock periods.
 */
module br_cdc_fifo_ctrl_1r1w_tb;

  parameter int Depth = 13;
  parameter int Width = 8;
  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterResetActive = 1;
  parameter int RamAddressDepthStages = 0;
  parameter int NumSyncStages = 3;
  parameter int PushClockPeriodNs = 10;
  parameter int PopClockPeriodNs = 16;
  parameter int NumRandomTransactions = 80;
  parameter int RandomPushIdleMax = 3;
  parameter int RandomPopIdleMax = 4;

  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2(Depth + 1);
  localparam int RamWriteLatency = RamAddressDepthStages + 1;
  localparam int RamReadLatency = RamAddressDepthStages;
  localparam int NumDirectedItems = Depth * 2 + 8;
  localparam int ScoreboardDepth = NumDirectedItems + NumRandomTransactions + Depth + 8;
  localparam int TimeoutPushCycles = 5000;
  localparam int TimeoutPopCycles = 5000;
  localparam int ResetSettlePushCycles = NumSyncStages + RegisterResetActive + 4;
  localparam int ResetSettlePopCycles = NumSyncStages + RegisterResetActive + 4;

  typedef struct packed {
    logic                  ready;
    logic                  valid;
    logic [     Width-1:0] data;
    logic                  full;
    logic [CountWidth-1:0] slots;
    logic                  ram_wr_valid;
    logic [ AddrWidth-1:0] ram_wr_addr;
    logic [     Width-1:0] ram_wr_data;
  } push_if_t;

  typedef struct packed {
    logic                  ready;
    logic                  valid;
    logic [     Width-1:0] data;
    logic                  empty;
    logic [CountWidth-1:0] items;
    logic                  ram_rd_addr_valid;
    logic [ AddrWidth-1:0] ram_rd_addr;
    logic                  ram_rd_data_valid;
    logic [     Width-1:0] ram_rd_data;
  } pop_if_t;

  logic push_clk;
  logic push_rst;
  push_if_t push_if;

  logic pop_clk;
  logic pop_rst;
  pop_if_t pop_if;

  logic [Width-1:0] expected_data[ScoreboardDepth];
  int expected_wr_idx;
  int expected_rd_idx;
  int expected_count;
  bit saw_push_backpressure;

  br_cdc_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RegisterResetActive(RegisterResetActive),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .EnableCoverPushBackpressure(1),
      .EnableAssertPushValidStability(1),
      .EnableAssertPushDataStability(1),
      .EnableAssertPushDataKnown(1),
      .EnableAssertFinalNotValid(1),
      .EnableAssertNoPushBackpressure(0)
  ) dut (
      .push_clk,
      .push_rst,
      .push_ready(push_if.ready),
      .push_valid(push_if.valid),
      .push_data(push_if.data),
      .push_full(push_if.full),
      .push_slots(push_if.slots),
      .push_ram_wr_valid(push_if.ram_wr_valid),
      .push_ram_wr_addr(push_if.ram_wr_addr),
      .push_ram_wr_data(push_if.ram_wr_data),
      .pop_clk,
      .pop_rst,
      .pop_ready(pop_if.ready),
      .pop_valid(pop_if.valid),
      .pop_data(pop_if.data),
      .pop_empty(pop_if.empty),
      .pop_items(pop_if.items),
      .pop_ram_rd_addr_valid(pop_if.ram_rd_addr_valid),
      .pop_ram_rd_addr(pop_if.ram_rd_addr),
      .pop_ram_rd_data_valid(pop_if.ram_rd_data_valid),
      .pop_ram_rd_data(pop_if.ram_rd_data)
  );

  br_ram_flops #(
      .Depth(Depth),
      .Width(Width),
      .NumReadPorts(1),
      .NumWritePorts(1),
      .AddressDepthStages(RamAddressDepthStages),
      .ReadDataDepthStages(0),
      .ReadDataWidthStages(0),
      .TileEnableBypass(0),
      .EnableMemReset(0),
      .UseStructuredGates(1),
      .EnableStructuredGatesDataQualification(1),
      .EnableAssertFinalNotValid(1)
  ) br_ram_flops (
      .wr_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(push_rst),
      .wr_valid(push_if.ram_wr_valid),
      .wr_addr(push_if.ram_wr_addr),
      .wr_data(push_if.ram_wr_data),
      .wr_word_en('1),
      .rd_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(pop_rst),
      .rd_addr_valid(pop_if.ram_rd_addr_valid),
      .rd_addr(pop_if.ram_rd_addr),
      .rd_data_valid(pop_if.ram_rd_data_valid),
      .rd_data(pop_if.ram_rd_data)
  );

`ifdef DUMP_WAVES
  initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, br_cdc_fifo_ctrl_1r1w_tb);
  end
`endif

  br_test_driver #(
      .ClockPeriodNs(PushClockPeriodNs),
      .ResetCycles  (14)
  ) td (
      .clk(push_clk),
      .rst(push_rst)
  );

  initial pop_clk = 1'b0;
  always #(PopClockPeriodNs / 2) pop_clk = ~pop_clk;
  always @(posedge pop_clk) pop_rst <= push_rst;

  task automatic init_interfaces();
    push_if.valid = 1'b0;
    push_if.data  = '0;
    pop_if.ready  = 1'b0;
  endtask

  task automatic reset_scoreboard();
    expected_wr_idx = 0;
    expected_rd_idx = 0;
    expected_count = 0;
    saw_push_backpressure = 0;
  endtask

  task automatic wait_push_cycles(input int cycles);
    repeat (cycles) @(negedge push_clk);
  endtask

  task automatic wait_pop_cycles(input int cycles);
    repeat (cycles) @(negedge pop_clk);
  endtask

  task automatic reset_dut();
    $assertoff;
    td.reset_dut();
    wait_push_cycles(ResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    $asserton;
  endtask

  task automatic expect_push(input logic [Width-1:0] data);
    td.check(expected_wr_idx < ScoreboardDepth, "scoreboard overflow");
    td.check(expected_count < Depth, "accepted push beyond FIFO depth");
    if ((expected_wr_idx < ScoreboardDepth) && (expected_count < Depth)) begin
      expected_data[expected_wr_idx] = data;
      expected_wr_idx++;
      expected_count++;
    end
  endtask

  task automatic expect_pop(input logic [Width-1:0] data);
    td.check(expected_count > 0, "unexpected pop");
    if (expected_count > 0) begin
      td.check(data === expected_data[expected_rd_idx], "pop data mismatch");
      expected_rd_idx++;
      expected_count--;
    end
  endtask

  task automatic push_timeout(input string message);
    repeat (TimeoutPushCycles) @(posedge push_clk);
    td.check(1'b0, message);
  endtask

  task automatic pop_timeout(input string message);
    repeat (TimeoutPopCycles) @(posedge pop_clk);
    td.check(1'b0, message);
  endtask

  task automatic drive_push(input logic [Width-1:0] data);
    fork : drive_push_timeout_guard
      push_timeout("push timed out");
      begin
        @(negedge push_clk);
        push_if.valid = 1'b1;
        push_if.data  = data;
        do begin
          @(posedge push_clk);
        end while (!push_if.ready);
        expect_push(data);
      end
    join_any
    disable drive_push_timeout_guard;

    @(negedge push_clk);
    push_if.valid = 1'b0;
    push_if.data  = '0;
  endtask

  task automatic drive_backpressured_push(input logic [Width-1:0] data);
    saw_push_backpressure = 0;
    fork : drive_backpressured_push_timeout_guard
      push_timeout("backpressured push timed out");
      begin
        @(negedge push_clk);
        push_if.valid = 1'b1;
        push_if.data  = data;
        do begin
          @(posedge push_clk);
          saw_push_backpressure |= !push_if.ready;
        end while (!push_if.ready);
        expect_push(data);
      end
    join_any
    disable drive_backpressured_push_timeout_guard;

    td.check(saw_push_backpressure, "push was not backpressured before acceptance");
    @(negedge push_clk);
    push_if.valid = 1'b0;
    push_if.data  = '0;
  endtask

  task automatic drive_pop(output logic [Width-1:0] data);
    logic [Width-1:0] popped_data;

    fork : drive_pop_timeout_guard
      pop_timeout("pop timed out");
      begin
        @(negedge pop_clk);
        pop_if.ready = 1'b1;
        do begin
          @(posedge pop_clk);
        end while (!pop_if.valid);
        popped_data = pop_if.data;
        expect_pop(popped_data);
      end
    join_any
    disable drive_pop_timeout_guard;

    data = popped_data;
    @(negedge pop_clk);
    pop_if.ready = 1'b0;
  endtask

  task automatic wait_for_pop_valid();
    fork : wait_for_pop_valid_timeout_guard
      pop_timeout("pop_valid timed out");
      begin
        while (!pop_if.valid) begin
          @(posedge pop_clk);
        end
      end
    join_any
    disable wait_for_pop_valid_timeout_guard;
  endtask

  task automatic wait_for_push_full();
    fork : wait_for_push_full_timeout_guard
      push_timeout("push_full timed out");
      begin
        while (!(push_if.full && !push_if.ready)) begin
          @(posedge push_clk);
        end
      end
    join_any
    disable wait_for_push_full_timeout_guard;
  endtask

  task automatic drain_all();
    logic [Width-1:0] data;

    while (expected_count > 0) begin
      drive_pop(data);
    end
  endtask

  task automatic drive_random_pushes();
    int idle_cycles;

    for (int i = 0; i < NumRandomTransactions; i++) begin
      idle_cycles = $urandom_range(RandomPushIdleMax, 0);
      wait_push_cycles(idle_cycles);
      drive_push(Width'($urandom));
    end
  endtask

  task automatic drive_random_pops();
    logic [Width-1:0] data;
    int idle_cycles;

    for (int i = 0; i < NumRandomTransactions; i++) begin
      idle_cycles = $urandom_range(RandomPopIdleMax, 0);
      wait_pop_cycles(idle_cycles);
      drive_pop(data);
    end
  endtask

  task automatic test_idle();
    reset_scoreboard();
    init_interfaces();
    reset_dut();

    td.check(push_if.ready, "idle: push_ready should be high after reset");
    td.check(!push_if.full, "idle: push_full should be low after reset");
    td.check_integer(int'(push_if.slots), Depth, "idle: push_slots mismatch");
    td.check(!pop_if.valid, "idle: pop_valid should be low after reset");
    td.check(pop_if.empty, "idle: pop_empty should be high after reset");
    td.check_integer(int'(pop_if.items), 0, "idle: pop_items mismatch");
  endtask

  task automatic test_single_push_pop();
    logic [Width-1:0] data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();

    drive_push(Width'('h5a));
    drive_pop(data);
  endtask

  task automatic test_fill_and_backpressure();
    logic [Width-1:0] data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();

    pop_if.ready = 1'b0;
    for (int i = 0; i < Depth; i++) begin
      drive_push(Width'(i + 1));
    end
    wait_for_push_full();

    fork
      drive_backpressured_push(Width'('ha5));
      drive_pop(data);
    join

    drain_all();
  endtask

  task automatic test_pop_stall();
    logic [Width-1:0] stalled_data;
    logic [Width-1:0] data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();

    drive_push(Width'('h3c));
    wait_for_pop_valid();

    stalled_data = pop_if.data;
    repeat (4) begin
      @(posedge pop_clk);
      td.check(pop_if.valid, "pop_stall: pop_valid dropped while stalled");
      td.check(pop_if.data === stalled_data, "pop_stall: pop_data changed while stalled");
    end

    drive_pop(data);
  endtask

  task automatic test_alternating();
    logic [Width-1:0] data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();

    for (int i = 0; i < NumDirectedItems; i++) begin
      drive_push(Width'(i));
      drive_pop(data);
    end
  endtask

  task automatic test_random();
    reset_scoreboard();
    init_interfaces();
    reset_dut();

    fork
      drive_random_pushes();
      drive_random_pops();
    join

    td.check_integer(expected_count, 0, "random: scoreboard should be empty");
  endtask

  task automatic run_all_tests();
    $display("Running test_idle");
    test_idle();
    $display("Running test_single_push_pop");
    test_single_push_pop();
    $display("Running test_fill_and_backpressure");
    test_fill_and_backpressure();
    $display("Running test_pop_stall");
    test_pop_stall();
    $display("Running test_alternating");
    test_alternating();
    $display("Running test_random");
    test_random();
  endtask

  initial begin
    static br_cdc_pkg::cdc_delay_mode_t cdc_delay_mode = br_cdc_pkg::CdcDelayNone;
    void'($value$plusargs("cdc_delay_mode=%d", cdc_delay_mode));
    $display("set cdc_delay_mode = %0s", cdc_delay_mode.name());
`ifdef SIMULATION
    br_cdc_pkg::cdc_delay_mode = cdc_delay_mode;
`endif

    pop_rst = 1'b1;
    init_interfaces();
    reset_scoreboard();

    run_all_tests();
    init_interfaces();
    wait_push_cycles(ResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    td.check_integer(expected_count, 0, "final: scoreboard should be empty");
    td.finish();
  end

endmodule
