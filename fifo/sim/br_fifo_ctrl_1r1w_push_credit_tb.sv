// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Testbench skeleton for br_fifo_ctrl_1r1w_push_credit, the FIFO controller
 * variant with a credit-valid push interface, ready-valid pop interface, and
 * external 1-read/1-write RAM. The bench is intended to use the existing
 * Bedrock credit sender as the push-side BFM adapter, br_ram_flops as the RAM
 * model, and a dynamic FIFO-order scoreboard for accepted push/pop payloads.
 *
 * Planned scenarios:
 * - Idle behavior and credit initialization after reset.
 * - Empty FIFO cut-through/bypass behavior.
 * - Fill-to-full operation and credit-based push backpressure.
 * - Dynamic credit withholding.
 * - Push credit return stalls.
 * - Push sender reset interaction with receiver reset signaling.
 * - Pop-side stall stability.
 * - Repeated alternating push/drain transitions.
 * - Bounded random push/pop transaction streams with independent BFMs.
 */
module br_fifo_ctrl_1r1w_push_credit_tb;

  // Parameters
  parameter int Depth = 13;
  parameter int Width = 8;
  parameter bit EnableBypass = 1;
  parameter int MaxCredit = Depth;
  parameter bit RegisterPushOutputs = 0;
  parameter bit RegisterPopOutputs = 0;
  parameter int RamReadLatency = 0;
  parameter int RamDepth = Depth;
  parameter bit EnableAssertPushDataKnown = 1;
  parameter bit EnableCoverCreditWithhold = 1;
  parameter bit EnableCoverPushSenderInReset = 1;
  parameter bit EnableCoverPushCreditStall = 1;
  parameter bit EnableAssertFinalNotValid = 1;
  parameter int NumRandomTransactions = 120;  // Payloads pushed and popped by test_random.
  parameter int RandomPushIdleMax = 3;  // Maximum random idle cycles before a random push.
  parameter int RandomPopIdleMax = 4;  // Maximum random idle cycles before a random pop.

  localparam int AddrWidth = $clog2(RamDepth) == 0 ? 1 : $clog2(RamDepth);
  localparam int CountWidth = $clog2(Depth + 1);
  localparam int CreditWidth = $clog2(MaxCredit + 1);
  localparam int NumDirectedItems = Depth * 2 + 8;
  localparam int TimeoutCycles = 2000;

  // Clock and Reset
  logic clk;  // Testbench clock driven by br_test_driver.
  logic rst;  // Synchronous active-high reset driven by br_test_driver.

  // Push ready-valid BFM interface before credit adaptation.
  logic push_ready;  // Credit sender readiness toward the testbench push BFM.
  logic push_valid;  // Testbench push-valid request into the credit sender.
  logic [Width-1:0] push_data;  // Testbench push payload into the credit sender.

  // Credit-valid push interface between the credit sender and DUT.
  logic dut_push_sender_in_reset;  // Credit sender reset indication toward the DUT.
  logic dut_push_receiver_in_reset;  // DUT reset indication back to the credit sender.
  logic dut_push_receiver_in_reset_d;  // Delayed DUT reset indication back to the credit sender.
  logic dut_push_credit_stall;  // Testbench stall control for DUT credit returns.
  logic dut_push_credit;  // DUT credit return to the credit sender.
  logic dut_push_credit_d;  // Delayed DUT credit return to the credit sender.
  logic dut_push_valid;  // Credit sender valid request into the DUT.
  logic [Width-1:0] dut_push_data;  // Credit sender payload into the DUT.
  logic push_sender_rst;  // Testbench-controlled reset applied only to the credit sender.
  logic credit_sender_rst;  // Combined main reset and push-sender-only reset.

  assign credit_sender_rst = rst || push_sender_rst;

  // Credit sender status.
  logic [CreditWidth-1:0] credit_initial_sender;  // Reset credit count for push BFM sender.
  logic [CreditWidth-1:0] credit_withhold_sender;  // Credits withheld inside push BFM sender.
  logic [CreditWidth-1:0] credit_count_sender;  // Current credit count inside push BFM sender.
  logic [CreditWidth-1:0] credit_available_sender;  // Sender credits available after withholding.

  // Pop ready-valid interface.
  logic pop_ready;  // Testbench ready on the DUT pop interface.
  logic pop_valid;  // DUT valid on the pop interface.
  logic [Width-1:0] pop_data;  // DUT payload on the pop interface.

  // Status outputs.
  logic full;  // DUT registered full status.
  logic full_next;  // DUT combinational next-cycle full status.
  logic [CountWidth-1:0] slots;  // DUT registered free-slot count.
  logic [CountWidth-1:0] slots_next;  // DUT combinational next-cycle free-slot count.
  logic empty;  // DUT registered empty status.
  logic empty_next;  // DUT combinational next-cycle empty status.
  logic [CountWidth-1:0] items;  // DUT registered occupied-item count.
  logic [CountWidth-1:0] items_next;  // DUT combinational next-cycle occupied-item count.

  // DUT push credit configuration and status.
  logic [CreditWidth-1:0] credit_initial_push;  // Reset credit count configured on the DUT.
  logic [CreditWidth-1:0] credit_withhold_push;  // Credits intentionally withheld by the DUT.
  logic [CreditWidth-1:0] credit_count_push;  // Current DUT-side credit counter value.
  logic [CreditWidth-1:0] credit_available_push;  // DUT-side credits available after withholding.

  // 1R1W RAM interface.
  logic ram_wr_valid;  // DUT write command valid for the external RAM.
  logic [AddrWidth-1:0] ram_wr_addr;  // DUT write address for the external RAM.
  logic [Width-1:0] ram_wr_data;  // DUT write payload for the external RAM.
  logic ram_rd_addr_valid;  // DUT read address valid for the external RAM.
  logic [AddrWidth-1:0] ram_rd_addr;  // DUT read address for the external RAM.
  logic ram_rd_data_valid;  // External RAM read response valid back to the DUT.
  logic [Width-1:0] ram_rd_data;  // External RAM read response payload back to the DUT.

  // Scoreboard and monitor state.
  logic [Width-1:0] expected_data[$];  // Dynamic FIFO-ordered expected pop payload queue.
  int expected_count;  // Scoreboard model of currently queued FIFO items.
  logic last_push_fire;  // Push transfer observed on the most recently sampled cycle.
  logic last_pop_fire;  // Pop handshake observed on the most recently sampled cycle.
  logic sampled_push_fire;  // Push transfer sampled by the monitor on the current cycle.
  logic sampled_pop_fire;  // Pop transfer sampled by the monitor on the current cycle.
  int sampled_expected_count;  // Scoreboard depth captured before current-cycle monitor updates.
  logic [Width-1:0] sampled_push_data;  // Push payload sampled by the monitor on the current cycle.
  logic [Width-1:0] sampled_pop_data;  // Pop payload sampled by the monitor on the current cycle.
  logic saw_credit_backpressure;  // Sticky bit recording a push request without sender credit.
  logic saw_credit_withhold;  // Sticky bit recording a scenario with nonzero withheld DUT credit.
  logic saw_push_credit_stall;  // Sticky bit recording a stalled DUT credit return.
  logic saw_push_sender_reset;  // Sticky bit recording sender reset assertion.
  logic random_pushes_done;  // Random push driver completion indication for random pop draining.
  logic [Width-1:0] last_pop_data;  // Pop payload captured on the most recent pop handshake.

  // Ready-valid to credit-valid adapter used as the push-side BFM.
  br_credit_sender #(
      .Width(Width),
      .MaxCredit(MaxCredit),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableCoverCreditWithhold(0),
      .EnableCoverPopReceiverInReset(EnableCoverPushSenderInReset),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid),
      .EnableAssertFinalMaxValue(0)
  ) br_credit_sender_push (
      .clk,
      .rst(credit_sender_rst),
      .push_ready,
      .push_valid,
      .push_data,
      .pop_sender_in_reset(dut_push_sender_in_reset),
      .pop_receiver_in_reset(dut_push_receiver_in_reset_d),
      .pop_credit(dut_push_credit_d),
      .pop_valid(dut_push_valid),
      .pop_data(dut_push_data),
      .credit_initial(credit_initial_sender),
      .credit_withhold(credit_withhold_sender),
      .credit_count(credit_count_sender),
      .credit_available(credit_available_sender)
  );

  // Instantiate the FIFO controller under test.
  br_fifo_ctrl_1r1w_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .EnableBypass(EnableBypass),
      .MaxCredit(MaxCredit),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamReadLatency(RamReadLatency),
      .RamDepth(RamDepth),
      .EnableAssertPushDataKnown(EnableAssertPushDataKnown),
      .EnableCoverCreditWithhold(EnableCoverCreditWithhold),
      .EnableCoverPushSenderInReset(EnableCoverPushSenderInReset),
      .EnableCoverPushCreditStall(EnableCoverPushCreditStall),
      .EnableAssertFinalNotValid(EnableAssertFinalNotValid)
  ) dut (
      .clk,
      .rst,
      .push_sender_in_reset(dut_push_sender_in_reset),
      .push_receiver_in_reset(dut_push_receiver_in_reset),
      .push_credit_stall(dut_push_credit_stall),
      .push_credit(dut_push_credit),
      .push_valid(dut_push_valid),
      .push_data(dut_push_data),
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
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .ram_wr_valid,
      .ram_wr_addr,
      .ram_wr_data,
      .ram_rd_addr_valid,
      .ram_rd_addr,
      .ram_rd_data_valid,
      .ram_rd_data
  );

  // Model a physical credit loop so returned credits cannot be spent in the
  // same cycle that the FIFO core creates them.
  br_delay_nr #(
      .NumStages(1),
      .Width(2)
  ) br_delay_nr_push_credit_return (
      .clk,
      .in({dut_push_credit, dut_push_receiver_in_reset}),
      .out({dut_push_credit_d, dut_push_receiver_in_reset_d}),
      .out_stages()
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
    $dumpvars(0, br_fifo_ctrl_1r1w_push_credit_tb);
  end
`endif

  br_test_driver td (
      .clk,
      .rst
  );

  task automatic init_interfaces();
    // Intent: Drive push, pop, credit configuration, and credit stall inputs to idle values.
    push_valid = 1'b0;
    push_data = '0;
    pop_ready = 1'b0;
    push_sender_rst = 1'b0;
    dut_push_credit_stall = 1'b0;
    credit_initial_sender = '0;
    credit_withhold_sender = '0;
    credit_initial_push = CreditWidth'(Depth);
    credit_withhold_push = '0;
  endtask

  task automatic reset_scoreboard();
    // Intent: Clear expected-data indices, occupancy, and sticky monitor observations.
    expected_data.delete();
    expected_count = 0;
    last_push_fire = 1'b0;
    last_pop_fire = 1'b0;
    sampled_push_fire = 1'b0;
    sampled_pop_fire = 1'b0;
    sampled_expected_count = 0;
    sampled_push_data = '0;
    sampled_pop_data = '0;
    saw_credit_backpressure = 1'b0;
    saw_credit_withhold = 1'b0;
    saw_push_credit_stall = 1'b0;
    saw_push_sender_reset = 1'b0;
    random_pushes_done = 1'b0;
    last_pop_data = '0;
  endtask

  task automatic timeout(input int cycles, input string message);
    // Intent: Guard a concurrent operation with a bounded simulation-time error.
    td.wait_cycles(cycles);
    td.check(1'b0, message);
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

  task automatic check_credit_status();
    // Intent: Compare DUT and sender credit status against the planned credit accounting model.
    td.check(int'(credit_count_push) <= MaxCredit, "DUT push credit count exceeded MaxCredit");
    td.check(int'(credit_count_sender) <= MaxCredit, "sender credit count exceeded MaxCredit");
  endtask

  task automatic expect_push(input logic [Width-1:0] data);
    // Intent: Record each accepted credit-valid push in the expected-data scoreboard.
    td.check(expected_count < Depth, "accepted push beyond FIFO depth");
    if (expected_count < Depth) begin
      expected_data.push_back(data);
      expected_count = expected_data.size();
    end
  endtask

  task automatic expect_pop(input logic [Width-1:0] data);
    // Intent: Check each accepted pop against FIFO ordering and expected payload data.
    logic [Width-1:0] expected;  // Payload expected at the head of the scoreboard queue.

    td.check(expected_data.size() > 0, "unexpected pop");
    if (expected_data.size() > 0) begin
      expected = expected_data.pop_front();
      td.check(data === expected, "pop data mismatch");
      expected_count = expected_data.size();
    end
  endtask

  task automatic monitor_push_credit_interface();
    // Intent: Sample credit-valid push transfers, returned credits, credit stalls, and sender reset.
    sampled_push_fire = dut.push_beat;
    sampled_push_data = dut.br_fifo_push_ctrl_credit.internal_data;
    last_push_fire = sampled_push_fire;
    saw_credit_backpressure |= push_valid && !push_ready;
    saw_credit_withhold |= |credit_withhold_push;
    saw_push_credit_stall |= dut_push_credit_stall;
    saw_push_sender_reset |= dut_push_sender_in_reset;
  endtask

  task automatic monitor_pop_interface();
    // Intent: Sample ready-valid pop handshakes and connect pop payloads to the scoreboard.
    sampled_pop_fire = pop_ready && pop_valid;
    sampled_pop_data = pop_data;
    last_pop_fire = sampled_pop_fire;
    if (sampled_pop_fire) begin
      last_pop_data = sampled_pop_data;
    end
  endtask

  task automatic monitor_enable();
    // Intent: Run push-credit, pop, status, and credit monitors while the test sequence is active.
    forever begin
      @(posedge clk);
      if (!rst) begin
        sampled_expected_count = expected_count;
        monitor_push_credit_interface();
        monitor_pop_interface();

        if (sampled_pop_fire) begin
          if (sampled_push_fire && (sampled_expected_count == 0)) begin
            td.check(sampled_pop_data === sampled_push_data, "bypass pop data mismatch");
          end else begin
            expect_pop(sampled_pop_data);
          end
        end

        if (sampled_push_fire && !(sampled_pop_fire && (sampled_expected_count == 0))) begin
          expect_push(sampled_push_data);
        end
      end

      @(negedge clk);
      if (!rst) begin
        check_status();
        check_credit_status();
      end
    end
  endtask

  task automatic drive_push(input logic [Width-1:0] data);
    // Intent: Push one item through the ready-valid BFM and credit sender as a blocking transaction.
    fork : drive_push_timeout_guard
      timeout(TimeoutCycles, "push timed out");
      begin
        @(negedge clk);
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
    // Intent: Pop one item from the DUT ready-valid interface as a blocking transaction.
    logic [Width-1:0] popped_data;  // Locally captured payload from the pop handshake.

    fork : drive_pop_timeout_guard
      timeout(TimeoutCycles, "pop timed out");
      begin
        @(negedge clk);
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

  task automatic set_push_credit_stall(input logic stall);
    // Intent: Control whether the DUT withholds returned push credits from the sender.
    dut_push_credit_stall = stall;
  endtask

  task automatic set_credit_withhold(input logic [CreditWidth-1:0] withhold);
    // Intent: Configure dynamic DUT-side credit withholding for credit accounting scenarios.
    credit_withhold_push = withhold;
  endtask

  task automatic set_push_sender_reset(input logic in_reset);
    // Intent: Assert or deassert the push sender reset indication seen by the DUT.
    push_sender_rst = in_reset;
  endtask

  task automatic wait_for_initial_credit();
    // Intent: Wait until the credit sender observes the receiver's configured initial credits.
    fork : wait_for_initial_credit_timeout_guard
      timeout(TimeoutCycles, "initial push credit timed out");
      begin
        while (credit_count_sender != credit_initial_push) begin
          td.wait_cycles();
        end
      end
    join_any
    disable wait_for_initial_credit_timeout_guard;
  endtask

  task automatic wait_for_pop_valid();
    // Intent: Wait until the DUT presents a pop-valid item without consuming it.
    fork : wait_for_pop_valid_timeout_guard
      timeout(TimeoutCycles, "pop_valid timed out");
      begin
        while (!pop_valid) begin
          td.wait_cycles();
        end
      end
    join_any
    disable wait_for_pop_valid_timeout_guard;
  endtask

  task automatic drain_all();
    // Intent: Pop all scoreboarded items or report a bounded drain timeout.
    fork : drain_all_timeout_guard
      timeout(TimeoutCycles, "drain timed out");
      begin
        pop_ready = 1'b1;
        while (expected_count > 0) begin
          td.wait_cycles();
        end
      end
    join_any
    disable drain_all_timeout_guard;

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
    random_pushes_done = 1'b1;
  endtask

  task automatic drive_random_pops();
    // Intent: Drive the random pop stream independently using the pop BFM.
    logic [Width-1:0] data;  // Payload returned by each random pop transaction.
    int idle_cycles;  // Random idle gap before the next pop transaction.

    while (!random_pushes_done || (expected_count > 0)) begin
      if (expected_count == 0) begin
        pop_ready = 1'b0;
        td.wait_cycles();
      end else begin
        idle_cycles = $urandom_range(RandomPopIdleMax, 0);
        pop_ready   = 1'b0;
        td.wait_cycles(idle_cycles);
        drive_pop(data);
      end
    end
  endtask

  task automatic test_idle();
    // Intent: Verify reset and idle behavior with no push/pop activity.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();
    repeat (4) begin
      td.wait_cycles();
    end
  endtask

  task automatic test_credit_initialization();
    // Intent: Verify initial credit return from the DUT receiver to the push credit sender.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();
    td.check_integer(int'(credit_count_sender), Depth, "sender initial credit mismatch");
    td.check(empty, "credit_initialization: FIFO should be empty after reset");
  endtask

  task automatic test_empty_cutthrough();
    // Intent: Exercise an initially-empty FIFO push with pop_ready asserted, including bypass cases.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    pop_ready = 1'b1;
    drive_push(Width'($urandom));
    drain_all();
  endtask

  task automatic test_fill_and_credit_backpressure();
    // Intent: Fill the FIFO to Depth and observe credit-based push backpressure at the sender.
    logic [Width-1:0] pending_data;  // Payload held stable while observing credit backpressure.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    pop_ready = 1'b0;
    for (int i = 0; i < Depth; i++) begin
      drive_push(Width'($urandom));
    end

    td.wait_cycles();
    td.check(full, "fill: FIFO should be full");
    td.check(!push_ready, "fill: push_ready should be low when sender has no credit");

    saw_credit_backpressure = 1'b0;
    pending_data = Width'($urandom);
    @(negedge clk);
    push_valid = 1'b1;
    push_data  = pending_data;
    td.wait_cycles();
    td.check(saw_credit_backpressure, "fill: push side did not observe credit backpressure");

    pop_ready = 1'b1;
    fork : fill_pending_push_timeout_guard
      timeout(TimeoutCycles, "pending backpressured push timed out");
      begin
        while (!(push_valid && push_ready)) begin
          @(posedge clk);
        end
      end
    join_any
    disable fill_pending_push_timeout_guard;

    @(negedge clk);
    push_valid = 1'b0;
    push_data  = '0;
    drain_all();
  endtask

  task automatic test_credit_withhold();
    // Intent: Configure nonzero credit withholding and verify reduced available push credit.
    logic [Width-1:0] data;  // Payload popped while one credit is withheld.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    set_credit_withhold(CreditWidth'(1));
    drive_push(Width'($urandom));
    drive_pop(data);
    td.wait_cycles(2);
    td.check(saw_credit_withhold, "credit_withhold: monitor did not observe withhold");
    td.check(int'(credit_count_sender) < Depth,
             "credit_withhold: sender recovered withheld credit");

    set_credit_withhold('0);
    wait_for_initial_credit();
  endtask

  task automatic test_push_credit_stall();
    // Intent: Stall push credit returns and verify the sender eventually experiences no-credit backpressure.
    logic [Width-1:0] data;  // Payload popped while push credit returns are stalled.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    drive_push(Width'($urandom));
    set_push_credit_stall(1'b1);
    drive_pop(data);
    td.wait_cycles(2);
    td.check(saw_push_credit_stall, "push_credit_stall: monitor did not observe stall");

    set_push_credit_stall(1'b0);
    wait_for_initial_credit();
  endtask

  task automatic test_push_sender_reset();
    // Intent: Assert push sender reset and verify receiver reset signaling and credit recovery behavior.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    set_push_sender_reset(1'b1);
    td.wait_cycles(2);
    td.check(saw_push_sender_reset, "push_sender_reset: DUT did not observe sender reset");

    set_push_sender_reset(1'b0);
    wait_for_initial_credit();
    td.check(empty, "push_sender_reset: FIFO should recover empty");
  endtask

  task automatic test_pop_stall();
    // Intent: Hold pop_ready low while data is available and check pop_data stability through stalls.
    logic [Width-1:0] stalled_data;  // Pop payload value expected to remain stable while stalled.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    pop_ready = 1'b0;
    drive_push(Width'($urandom));
    wait_for_pop_valid();

    stalled_data = pop_data;
    repeat (4) begin
      td.wait_cycles();
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
    wait_for_initial_credit();

    for (int i = 0; i < NumDirectedItems; i++) begin
      pop_ready = 1'b0;
      drive_push(Width'($urandom));
      drain_all();
    end
  endtask

  task automatic test_random();
    // Intent: Run bounded pseudo-random push and pop transaction streams with independent BFMs.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_for_initial_credit();

    fork : random_test_timeout_guard
      timeout(TimeoutCycles * NumRandomTransactions, "random test timed out");
      begin
        fork
          drive_random_pushes();
          drive_random_pops();
        join
      end
    join_any
    disable random_test_timeout_guard;

    init_interfaces();
    drain_all();
  endtask

  task automatic run_all_tests();
    // Intent: Sequence reset, directed scenarios, random traffic, final drain, and finish reporting.
    $display("Running test_idle");
    test_idle();
    $display("Running test_credit_initialization");
    test_credit_initialization();
    $display("Running test_empty_cutthrough");
    test_empty_cutthrough();
    $display("Running test_fill_and_credit_backpressure");
    test_fill_and_credit_backpressure();
    $display("Running test_credit_withhold");
    test_credit_withhold();
    $display("Running test_push_credit_stall");
    test_push_credit_stall();
    $display("Running test_push_sender_reset");
    test_push_sender_reset();
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
    td.check(expected_data.size() == 0, "final: scoreboard should be empty");
    td.finish();
  end

endmodule
