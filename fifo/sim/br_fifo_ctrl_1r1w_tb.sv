// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Testbench for br_fifo_ctrl_1r1w, the ready-valid FIFO controller for an
 * external 1-read/1-write RAM. The bench uses the existing Bedrock RAM model
 * and scoreboards every accepted push/pop transaction to check ordering,
 * payload integrity, occupancy status, and backpressure behavior.
 *
 * Covered scenarios:
 * - Idle behavior after reset.
 * - Empty FIFO cut-through/bypass behavior.
 * - Fill-to-full operation and push backpressure.
 * - Pop-side stall stability.
 * - Repeated alternating push/drain transitions.
 * - Bounded random push/pop transaction streams with independent BFMs.
 */
module br_fifo_ctrl_1r1w_tb;

  // Parameters
  parameter int Depth = 13;
  parameter int Width = 8;
  parameter int EnableBypass = 1;
  parameter int RegisterPopOutputs = 0;
  parameter int RamReadLatency = 0;
  parameter int RamDepth = Depth;
  // Assertion enables are surfaced so each generated test parameter set can
  // choose the legal assertion mode for its scenario.
  parameter bit EnableCoverPushBackpressure = 1;
  parameter bit EnableAssertPushValidStability = 1;
  parameter bit EnableAssertPushDataStability = 1;
  parameter bit EnableAssertPushDataKnown = 1;
  parameter bit EnableAssertFinalNotValid = 1;
  parameter bit EnableAssertNoPushBackpressure = 0;
  parameter int NumRandomTransactions = 120;  // Payloads pushed and popped by test_random.
  parameter int RandomPushIdleMax = 3;  // Maximum random idle cycles before a random push.
  parameter int RandomPopIdleMax = 4;  // Maximum random idle cycles before a random pop.

  localparam int AddrWidth = $clog2(RamDepth) == 0 ? 1 : $clog2(RamDepth);
  localparam int CountWidth = $clog2(Depth + 1);
  localparam int NumDirectedItems = Depth * 2 + 8;
  localparam int ScoreboardDepth = NumDirectedItems + NumRandomTransactions + Depth;
  localparam int TimeoutCycles = 2000;

  // Clock and Reset
  logic clk;  // Testbench clock driven by br_test_driver.
  logic rst;  // Synchronous active-high reset driven by br_test_driver.

  // Push Interface
  logic push_ready;  // DUT backpressure indication for the push ready-valid interface.
  logic push_valid;  // Testbench valid on the push ready-valid interface.
  logic [Width-1:0] push_data;  // Testbench payload on the push ready-valid interface.

  // Pop Interface
  logic pop_ready;  // Testbench ready on the pop ready-valid interface.
  logic pop_valid;  // DUT valid on the pop ready-valid interface.
  logic [Width-1:0] pop_data;  // DUT payload on the pop ready-valid interface.

  // Status Outputs
  logic full;  // DUT registered full status.
  logic full_next;  // DUT combinational next-cycle full status.
  logic [CountWidth-1:0] slots;  // DUT registered free-slot count.
  logic [CountWidth-1:0] slots_next;  // DUT combinational next-cycle free-slot count.
  logic empty;  // DUT registered empty status.
  logic empty_next;  // DUT combinational next-cycle empty status.
  logic [CountWidth-1:0] items;  // DUT registered occupied-item count.
  logic [CountWidth-1:0] items_next;  // DUT combinational next-cycle occupied-item count.

  // 1R1W RAM Interface
  logic ram_wr_valid;  // DUT write command valid for the external RAM.
  logic [AddrWidth-1:0] ram_wr_addr;  // DUT write address for the external RAM.
  logic [Width-1:0] ram_wr_data;  // DUT write payload for the external RAM.
  logic ram_rd_addr_valid;  // DUT read address valid for the external RAM.
  logic [AddrWidth-1:0] ram_rd_addr;  // DUT read address for the external RAM.
  logic ram_rd_data_valid;  // External RAM read response valid back to the DUT.
  logic [Width-1:0] ram_rd_data;  // External RAM read response payload back to the DUT.

  // Scoreboard and monitor state.
  logic [Width-1:0] expected_data[ScoreboardDepth];  // FIFO-ordered expected pop payloads.
  int expected_wr_idx;  // Next expected_data slot to write after an accepted push.
  int expected_rd_idx;  // Next expected_data slot to read after an accepted pop.
  int expected_count;  // Scoreboard model of currently queued FIFO items.
  logic last_push_fire;  // Push handshake observed on the most recently sampled cycle.
  logic last_pop_fire;  // Pop handshake observed on the most recently sampled cycle.
  logic saw_push_backpressure;  // Sticky bit recording push_valid while push_ready is low.
  logic [Width-1:0] last_pop_data;  // Pop payload captured on the most recent pop handshake.

  // Instantiate the FIFO controller under test.
  br_fifo_ctrl_1r1w #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .RamDepth(RamDepth),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableAssertPushValidStability(EnableAssertPushValidStability),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) dut (
      .clk,
      .rst,
      .push_ready,
      .push_valid,
      .push_data,
      .pop_ready,
      .pop_valid,
      .pop_data,
      .full,
      .full_next,
      .slots,
      .slots_next,
      .empty,
      .empty_next,
      .items,
      .items_next,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data
  );

  // Existing Bedrock flop RAM used as the external RAM for the controller.
  br_ram_flops #(
      .Depth(RamDepth),
      .Width(Width),
      .NumReadPorts(1),
      .NumWritePorts(1),
      .AddressDepthStages(RamReadLatency),
      .ReadDataDepthStages(0),
      .ReadDataWidthStages(0),
      // FIFO control should avoid same-cycle read/write hazards at the same address.
      .TileEnableBypass(0),
      .EnableMemReset(0),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) br_ram_flops (
      .wr_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(rst),
      .wr_valid(ram_wr_valid),
      .wr_addr(ram_wr_addr),
      .wr_data(ram_wr_data),
      .wr_word_en('1),
      .rd_clk(clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(rst),
      .rd_addr_valid(ram_rd_addr_valid),
      .rd_addr(ram_rd_addr),
      .rd_data_valid(ram_rd_data_valid),
      .rd_data(ram_rd_data)
  );

`ifdef DUMP_WAVES
  initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, br_fifo_ctrl_1r1w_tb);
  end
`endif

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic init_interfaces();
    // Intent: Drive push and pop testbench inputs to known idle values before reset.
    push_valid = 1'b0;
    push_data  = '0;
    pop_ready  = 1'b0;
  endtask

  task automatic reset_scoreboard();
    // Intent: Clear expected-data indices and occupancy tracking before each independent scenario.
    expected_wr_idx = 0;
    expected_rd_idx = 0;
    expected_count = 0;
    last_push_fire = 1'b0;
    last_pop_fire = 1'b0;
    saw_push_backpressure = 1'b0;
    last_pop_data = '0;
  endtask

  task automatic check_status();
    // Intent: Compare full/empty/items/slots status against the scoreboard occupancy model.
    td.check_integer(int'(items), expected_count, "items mismatch");
    td.check_integer(int'(slots), Depth - expected_count, "slots mismatch");
    td.check(empty == (expected_count == 0), "empty mismatch");
    td.check(full == (expected_count == Depth), "full mismatch");
    td.check_integer(int'(items) + int'(slots), Depth, "items plus slots mismatch");
    td.check_integer(int'(items_next) + int'(slots_next), Depth, "next items plus slots mismatch");
  endtask

  task automatic expect_push(input logic [Width-1:0] data);
    // Intent: Record each accepted push in the expected-data scoreboard.
    td.check(expected_wr_idx < ScoreboardDepth, "scoreboard overflow");
    td.check(expected_count < Depth, "accepted push beyond FIFO depth");
    if ((expected_wr_idx < ScoreboardDepth) && (expected_count < Depth)) begin
      expected_data[expected_wr_idx] = data;
      expected_wr_idx++;
      expected_count++;
    end
  endtask

  task automatic expect_pop(input logic [Width-1:0] data);
    // Intent: Check each accepted pop against FIFO ordering and expected payload data.
    td.check(expected_count > 0, "unexpected pop");
    if (expected_count > 0) begin
      td.check(data === expected_data[expected_rd_idx], "pop data mismatch");
      expected_rd_idx++;
      expected_count--;
    end
  endtask

  task automatic monitor_push_pop_interfaces();
    // Intent: Isolate ready-valid handshake detection and connect sampled push/pop data to
    // expect_push and expect_pop scoreboard updates.
    logic push_fire;  // Push handshake observed in the sampled cycle.
    logic pop_fire;  // Pop handshake observed in the sampled cycle.
    logic pop_from_current_push;  // Same-cycle empty FIFO push/pop bypass indication.

    push_fire = push_valid && push_ready;
    pop_fire = pop_ready && pop_valid;
    pop_from_current_push = push_fire && pop_fire && (expected_count == 0);

    last_push_fire = push_fire;
    last_pop_fire = pop_fire;
    saw_push_backpressure |= push_valid && !push_ready;

    if (pop_fire) begin
      last_pop_data = pop_data;
      if (pop_from_current_push) begin
        td.check(pop_data === push_data, "bypass pop data mismatch");
      end else begin
        expect_pop(pop_data);
      end
    end

    if (push_fire && !pop_from_current_push) begin
      expect_push(push_data);
    end
  endtask

  task automatic monitor_enable();
    // Intent: Run the shared monitor/checker thread while reset is deasserted.
    forever begin
      @(posedge clk);
      if (!rst) begin
        monitor_push_pop_interfaces();
      end
      @(negedge clk);
      if (!rst) begin
        check_status();
      end
    end
  endtask

  task automatic timeout(input int cycles, input string message);
    // Intent: Guard a concurrent operation with a bounded simulation-time error.
    repeat (cycles) begin
      @(negedge clk);
    end
    td.check(1'b0, message);
  endtask

  task automatic drive_push(input logic [Width-1:0] data);
    // Intent: Push one item as a blocking ready-valid BFM transaction.
    fork : drive_push_timeout_guard
      timeout(TimeoutCycles, "push timed out");
      begin
        push_valid = 1'b1;
        push_data  = data;
        do begin
          @(posedge clk);
        end while (!(push_valid && push_ready));
      end
    join_any
    disable drive_push_timeout_guard;

    @(negedge clk);
    push_valid = 1'b0;
    push_data  = '0;
  endtask

  task automatic drive_pop(output logic [Width-1:0] data);
    // Intent: Pop one item as a blocking ready-valid BFM transaction.
    logic [Width-1:0] popped_data;  // Locally captured payload from the pop handshake.

    fork : drive_pop_timeout_guard
      timeout(TimeoutCycles, "pop timed out");
      begin
        pop_ready = 1'b1;
        do begin
          @(posedge clk);
        end while (!(pop_ready && pop_valid));
        popped_data = pop_data;
      end
    join_any
    disable drive_pop_timeout_guard;

    data = popped_data;
    @(negedge clk);
    pop_ready = 1'b0;
  endtask

  task automatic drive_random_pushes();
    // Intent: Drive the random push stream independently using the push BFM.
    int idle_cycles;  // Random idle gap before the next push transaction.

    for (int i = 0; i < NumRandomTransactions; i++) begin
      idle_cycles = $urandom_range(RandomPushIdleMax, 0);
      push_valid  = 1'b0;
      push_data   = '0;
      td.wait_cycles(idle_cycles);
      drive_push(Width'($urandom));
    end
  endtask

  task automatic drive_random_pops();
    // Intent: Drive the random pop stream independently using the pop BFM.
    logic [Width-1:0] data;  // Payload returned by each random pop transaction.
    int idle_cycles;  // Random idle gap before the next pop transaction.

    for (int i = 0; i < NumRandomTransactions; i++) begin
      idle_cycles = $urandom_range(RandomPopIdleMax, 0);
      pop_ready   = 1'b0;
      td.wait_cycles(idle_cycles);
      drive_pop(data);
    end
  endtask

  task automatic sample_idle_cycle();
    // Intent: Advance one cycle with both testbench ready-valid drivers idle.
    push_valid = 1'b0;
    push_data  = '0;
    pop_ready  = 1'b0;
    td.wait_cycles();
  endtask

  task automatic set_pop_ready(input logic ready);
    // Intent: Hold pop_ready at a directed value for scenarios that need stalls or cut-through.
    pop_ready = ready;
  endtask

  task automatic wait_for_pop_valid();
    // Intent: Wait for the DUT to present a valid pop item without consuming it.
    fork : wait_for_pop_valid_timeout_guard
      timeout(TimeoutCycles, "pop_valid timed out");
      begin
        while (!pop_valid) begin
          sample_idle_cycle();
        end
      end
    join_any
    disable wait_for_pop_valid_timeout_guard;
  endtask

  task automatic drain_all();
    // Intent: Keep popping until all scoreboarded items are observed or timeout expires.
    fork : drain_all_timeout_guard
      timeout(TimeoutCycles, "drain timed out");
      begin
        pop_ready = 1'b1;
        while (expected_count > 0) begin
          @(posedge clk);
        end
      end
    join_any
    disable drain_all_timeout_guard;

    @(negedge clk);
    pop_ready = 1'b0;
  endtask

  task automatic test_idle();
    // Intent: Verify reset and idle behavior with no push/pop activity.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    repeat (4) begin
      sample_idle_cycle();
    end
  endtask

  task automatic test_empty_cutthrough();
    // Intent: Exercise an initially-empty FIFO push with pop_ready asserted, including bypass cases.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    set_pop_ready(1'b1);
    drive_push(Width'($urandom));
    set_pop_ready(1'b0);
    drain_all();
  endtask

  task automatic test_fill_and_backpressure();
    // Intent: Fill the FIFO to Depth and check full/backpressure behavior. Parameter sets for
    // this scenario should disable EnableAssertNoPushBackpressure and enable backpressure coverage.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    set_pop_ready(1'b0);
    for (int i = 0; i < Depth; i++) begin
      drive_push(Width'($urandom));
    end
    td.check(full, "fill: FIFO should be full");
    td.check(!push_ready, "fill: push_ready should be low when full");

    set_pop_ready(1'b1);
    saw_push_backpressure = 1'b0;
    drive_push(Width'($urandom));
    td.check(saw_push_backpressure, "full_backpressure: push was not backpressured");

    drain_all();
  endtask

  task automatic test_pop_stall();
    // Intent: Hold pop_ready low while data is available and check pop_data stability through stalls.
    logic [Width-1:0] stalled_data;  // Pop payload value expected to remain stable while stalled.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    set_pop_ready(1'b0);
    drive_push(Width'($urandom));
    wait_for_pop_valid();

    stalled_data = pop_data;
    repeat (4) begin
      sample_idle_cycle();
      td.check(pop_valid, "pop_stall: pop_valid dropped while stalled");
      td.check(pop_data === stalled_data, "pop_stall: pop_data changed while stalled");
    end

    drain_all();
  endtask

  task automatic test_alternating();
    // Intent: Alternate single pushes and drains to cover repeated empty-to-nonempty transitions.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    for (int i = 0; i < NumDirectedItems; i++) begin
      set_pop_ready(1'b0);
      drive_push(Width'($urandom));
      drain_all();
    end
  endtask

  task automatic test_random();
    // Intent: Run deterministic random push/pop transaction streams with independent BFMs.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    fork
      drive_random_pushes();
      drive_random_pops();
    join

    init_interfaces();
    drain_all();
  endtask

  task automatic run_all_tests();
    // Intent: Sequence reset, directed scenarios, random traffic, final drain, and finish reporting.
    $display("Running test_idle");
    test_idle();
    $display("Running test_empty_cutthrough");
    test_empty_cutthrough();
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
    init_interfaces();
    reset_scoreboard();
    fork
      monitor_enable();
    join_none
    run_all_tests();
    td.check(expected_count == 0, "final: scoreboard should be empty");
    td.finish();
  end

endmodule
