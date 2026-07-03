// SPDX-License-Identifier: Apache-2.0


`timescale 1ns / 1ps

/*
 * Directed simulation testbench for br_cdc_fifo_ctrl_1r1w_push_credit.
 *
 * Scope:
 * - Reset and idle status checks in both clock domains.
 * - Initial push-credit recovery through br_credit_sender.
 * - Directed push/pop, credit backpressure, credit withhold/stall, and pop-stall behavior.
 * - Payload ordering checks for every accepted pop.
 * - External 1R1W RAM timing through br_ram_flops.
 * - Bazel-swept RAM latency, pop/push-output registration, CDC synchronizer depth,
 *   structured-gate data qualification, and CDC delay mode.
 * - Default and plusarg-selected push/pop clock periods.
 */
module br_cdc_fifo_ctrl_1r1w_push_credit_tb;

  parameter bit RegisterPopOutputs = 0;
  parameter bit RegisterPushOutputs = 0;
  parameter bit RegisterResetActive = 1;
  parameter int RamAddressDepthStages = 0;
  parameter int NumSyncStages = 3;
  parameter bit EnableStructuredGatesDataQualification = 1;
  parameter int PushClockPeriodNs = 10;
  parameter int PopClockPeriodNs = 16;
  parameter int RandomPushIdleMax = 3;
  parameter int RandomPopIdleMax = 4;

  localparam int PropDelay = 3;
  localparam int Depth = 13;
  localparam int Width = 8;
  localparam int AddrWidth = $clog2(Depth);
  localparam int CountWidth = $clog2(Depth + 1);
  localparam int CreditWidth = $clog2(Depth + 1);
  localparam int RamWriteLatency = RamAddressDepthStages + 1;
  localparam int RamReadLatency = RamAddressDepthStages;
  localparam int NumDirectedItems = Depth * 2 + 8;
  localparam int NumRandomTransactions = 100;
  localparam int TimeoutPushCycles = 50000;
  localparam int TimeoutPopCycles = 50000;
  localparam int PushCountSettleCycles = (RegisterResetActive + 1 > RamWriteLatency) ?
      RegisterResetActive + 1 : RamWriteLatency;
  localparam int PopCountSettleCycles = RegisterResetActive + 1;
  localparam int ResetAssertPushCycles = PushCountSettleCycles + NumSyncStages + PropDelay + 4;
  localparam int ResetAssertPopCycles = PopCountSettleCycles + NumSyncStages + 4;
  localparam int ResetSettlePushCycles = NumSyncStages + RegisterResetActive + PropDelay + 4;
  localparam int ResetSettlePopCycles = NumSyncStages + RegisterResetActive + RamReadLatency +
      32'(RegisterPopOutputs) + 4;
  localparam int ResetPreIdlePushCycles = PushCountSettleCycles + NumSyncStages + PropDelay + 2;
  localparam int ResetPreIdlePopCycles = PopCountSettleCycles + NumSyncStages + RamReadLatency +
      32'(RegisterPopOutputs) + 2;
  localparam int SenderResetAssertPushCycles = ResetAssertPushCycles + PropDelay + 2;
  localparam int SenderResetSettlePushCycles = ResetSettlePushCycles + PropDelay + 2;
  function automatic int random_clock_period_ns();
    return $urandom_range(101, 7);
  endfunction

  // Ready-valid stimulus interface into br_credit_sender, before credit adaptation.
  typedef struct packed {
    logic ready;
    logic valid;
    logic [Width-1:0] data;
  } credit_sender_push_if_t;

  typedef struct packed {
    logic                  credit;
    logic                  valid;
    logic [Width-1:0]      data;
    logic                  full;
    logic [CountWidth-1:0] slots;
    logic                  ram_wr_valid;
    logic [AddrWidth-1:0]  ram_wr_addr;
    logic [Width-1:0]      ram_wr_data;
  } dut_push_if_t;

  typedef struct packed {
    logic                  ready;
    logic                  valid;
    logic [Width-1:0]      data;
    logic                  empty;
    logic [CountWidth-1:0] items;
    logic                  ram_rd_addr_valid;
    logic [AddrWidth-1:0]  ram_rd_addr;
    logic                  ram_rd_data_valid;
    logic [Width-1:0]      ram_rd_data;
  } dut_pop_if_t;

  typedef enum {
    CreditCheckIdle,
    CreditCheckCreditInitialization,
    CreditCheckPushMonitor,
    CreditCheckFinal
  } credit_check_status_t;

  function automatic string credit_check_status_name(input credit_check_status_t status);
    case (status)
      CreditCheckIdle:                 return "idle";
      CreditCheckCreditInitialization: return "credit_initialization";
      CreditCheckPushMonitor:          return "push_monitor";
      CreditCheckFinal:                return "final";
      default:                         return "unknown";
    endcase
  endfunction

  logic push_clk = 1'b0;
  logic push_rst = 1'b1;
  credit_sender_push_if_t credit_sender_push_if;
  dut_push_if_t dut_push_if;

  logic pop_clk = 1'b0;
  logic pop_rst = 1'b1;
  dut_pop_if_t dut_pop_if;

  logic td_clk;
  logic td_rst;
  time push_clock_half_period;
  time pop_clock_half_period;
  int selected_push_clock_period_ns;
  int selected_pop_clock_period_ns;
  bit clock_periods_configured = 1'b0;

  dut_push_if_t dut_push_if_d;
  logic credit_sender_rst;
  logic push_sender_rst;
  logic push_sender_in_reset;
  logic push_sender_in_reset_d;
  logic push_receiver_in_reset;
  logic push_receiver_in_reset_d;
  logic push_credit_stall;
  logic [CreditWidth-1:0] credit_initial_sender;
  logic [CreditWidth-1:0] credit_withhold_sender;
  logic [CreditWidth-1:0] credit_count_sender;
  logic [CreditWidth-1:0] credit_initial_push;
  logic [CreditWidth-1:0] credit_withhold_push;
  logic [CreditWidth-1:0] credit_count_push;
  logic [CreditWidth-1:0] credit_available_push;
  logic push_either_rst;

  logic [Width-1:0] expected_data[$];
  int expected_count;
  bit saw_credit_backpressure;
  bit saw_credit_withhold;
  bit saw_push_credit_stall;
  bit saw_push_sender_reset;
  bit random_pushes_done;
  bit reset_in_progress;
  bit reset_seen;

  assign credit_sender_rst = push_rst || push_sender_rst;
  // Reset the push-side RAM model while the delayed sender reset is visible at the DUT.
  assign push_either_rst   = push_rst || push_sender_in_reset_d;

  br_cdc_fifo_ctrl_1r1w_push_credit #(
      .Depth(Depth),
      .Width(Width),
      .RegisterPopOutputs(RegisterPopOutputs),
      .RamWriteLatency(RamWriteLatency),
      .RamReadLatency(RamReadLatency),
      .NumSyncStages(NumSyncStages),
      .MaxCredit(Depth),
      .RegisterPushOutputs(RegisterPushOutputs),
      .RegisterResetActive(RegisterResetActive),
      .EnableCoverCreditWithhold(1),
      .EnableCoverPushSenderInReset(1),
      .EnableCoverPushCreditStall(1),
      .EnableAssertPushDataKnown(1),
      .EnableAssertFinalNotValid(1)
  ) dut (
      .push_clk,
      .push_rst,
      .push_sender_in_reset(push_sender_in_reset_d),
      .push_receiver_in_reset(push_receiver_in_reset),
      .push_credit_stall,
      .push_credit(dut_push_if.credit),
      .push_valid(dut_push_if_d.valid),
      .push_data(dut_push_if_d.data),
      .push_full(dut_push_if.full),
      .push_slots(dut_push_if.slots),
      .credit_initial_push,
      .credit_withhold_push,
      .credit_count_push,
      .credit_available_push,
      .push_ram_wr_valid(dut_push_if.ram_wr_valid),
      .push_ram_wr_addr(dut_push_if.ram_wr_addr),
      .push_ram_wr_data(dut_push_if.ram_wr_data),
      .pop_clk,
      .pop_rst,
      .pop_ready(dut_pop_if.ready),
      .pop_valid(dut_pop_if.valid),
      .pop_data(dut_pop_if.data),
      .pop_empty(dut_pop_if.empty),
      .pop_items(dut_pop_if.items),
      .pop_ram_rd_addr_valid(dut_pop_if.ram_rd_addr_valid),
      .pop_ram_rd_addr(dut_pop_if.ram_rd_addr),
      .pop_ram_rd_data_valid(dut_pop_if.ram_rd_data_valid),
      .pop_ram_rd_data(dut_pop_if.ram_rd_data)
  );

  br_credit_sender #(
      .Width(Width),
      .MaxCredit(Depth),
      .EnableAssertPushValidStability(1),
      .EnableAssertPushDataStability(1),
      .EnableCoverCreditWithhold(0),
      .EnableCoverPopReceiverInReset(1),
      .EnableAssertFinalNotValid(1),
      .EnableAssertFinalMaxValue(0)
  ) br_credit_sender_push (
      .clk(push_clk),
      .rst(credit_sender_rst),
      .push_ready(credit_sender_push_if.ready),
      .push_valid(credit_sender_push_if.valid),
      .push_data(credit_sender_push_if.data),
      .pop_sender_in_reset(push_sender_in_reset),
      .pop_receiver_in_reset(push_receiver_in_reset_d),
      .pop_credit(dut_push_if_d.credit),
      .pop_valid(dut_push_if.valid),
      .pop_data(dut_push_if.data),
      .credit_initial(credit_initial_sender),
      .credit_withhold(credit_withhold_sender),
      .credit_count(credit_count_sender),
      .credit_available()
  );

  br_delay_nr #(
      .NumStages(PropDelay),
      .Width(Width + 2)
  ) br_delay_nr_to_fifo (
      .clk(push_clk),
      .in({dut_push_if.valid, dut_push_if.data, push_sender_in_reset}),
      .out({dut_push_if_d.valid, dut_push_if_d.data, push_sender_in_reset_d}),
      .out_stages()
  );

  br_delay_nr #(
      .NumStages(PropDelay),
      .Width(2)
  ) br_delay_nr_from_fifo (
      .clk(push_clk),
      .in({dut_push_if.credit, push_receiver_in_reset}),
      .out({dut_push_if_d.credit, push_receiver_in_reset_d}),
      .out_stages()
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
      .EnableStructuredGatesDataQualification(EnableStructuredGatesDataQualification),
      .EnableAssertFinalNotValid(1)
  ) br_ram_flops (
      .wr_clk(push_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .wr_rst(push_either_rst),
      .wr_valid(dut_push_if.ram_wr_valid),
      .wr_addr(dut_push_if.ram_wr_addr),
      .wr_data(dut_push_if.ram_wr_data),
      .wr_word_en('1),
      .rd_clk(pop_clk),  // ri lint_check_waive SAME_CLOCK_NAME
      .rd_rst(pop_rst),
      .rd_addr_valid(dut_pop_if.ram_rd_addr_valid),
      .rd_addr(dut_pop_if.ram_rd_addr),
      .rd_data_valid(dut_pop_if.ram_rd_data_valid),
      .rd_data(dut_pop_if.ram_rd_data)
  );

  br_test_driver td (
      .clk(td_clk),
      .rst(td_rst)
  );

  task automatic validate_clock_periods();
    if (selected_push_clock_period_ns < 1) begin
      $fatal(1, "push clock period must be at least 1 ns");
    end
    if (selected_pop_clock_period_ns < 1) begin
      $fatal(1, "pop clock period must be at least 1 ns");
    end
  endtask

  task automatic configure_clock_periods();
    selected_push_clock_period_ns = PushClockPeriodNs;
    selected_pop_clock_period_ns  = PopClockPeriodNs;

    void'($value$plusargs("push_clock_period_ns=%d", selected_push_clock_period_ns));
    void'($value$plusargs("pop_clock_period_ns=%d", selected_pop_clock_period_ns));

    if (selected_push_clock_period_ns == -1) begin
      selected_push_clock_period_ns = random_clock_period_ns();
      $display("push_clock_period_ns=-1 generated random push period");
    end
    if (selected_pop_clock_period_ns == -1) begin
      selected_pop_clock_period_ns = random_clock_period_ns();
      $display("pop_clock_period_ns=-1 generated random pop period");
    end

    validate_clock_periods();
    push_clock_half_period = (selected_push_clock_period_ns * 1ns) / 2;
    pop_clock_half_period  = (selected_pop_clock_period_ns * 1ns) / 2;
    $display("push_clock_period_ns=%0d pop_clock_period_ns=%0d", selected_push_clock_period_ns,
             selected_pop_clock_period_ns);
  endtask

  initial begin
    clock_periods_configured = 1'b0;
    configure_clock_periods();
    clock_periods_configured = 1'b1;
  end

  initial begin
    wait (clock_periods_configured);
    forever #(push_clock_half_period) push_clk = ~push_clk;
  end

  initial begin
    wait (clock_periods_configured);
    forever #(pop_clock_half_period) pop_clk = ~pop_clk;
  end

  initial begin
    init_interfaces();
  end

  task automatic init_interfaces();
    credit_sender_push_if.valid = 1'b0;
    credit_sender_push_if.data = '0;
    dut_pop_if.ready = 1'b0;
    push_sender_rst = 1'b0;
    push_credit_stall = 1'b0;
    credit_initial_sender = '0;
    credit_withhold_sender = '0;
    credit_initial_push = CreditWidth'(Depth);
    credit_withhold_push = '0;
  endtask

  task automatic reset_scoreboard();
    expected_data.delete();
    expected_count = 0;
    saw_credit_backpressure = 1'b0;
    saw_credit_withhold = 1'b0;
    saw_push_credit_stall = 1'b0;
    saw_push_sender_reset = 1'b0;
    random_pushes_done = 1'b0;
    reset_in_progress = 1'b0;
  endtask

  task automatic wait_push_cycles(input int cycles);
    repeat (cycles) @(posedge push_clk);
  endtask

  task automatic wait_pop_cycles(input int cycles);
    repeat (cycles) @(posedge pop_clk);
  endtask

  task automatic wait_for_reset_safe_idle();
    if (reset_seen) begin
      fork
        wait_push_cycles(ResetPreIdlePushCycles);
        wait_pop_cycles(ResetPreIdlePopCycles);
      join
    end
  endtask

  task automatic reset_dut();
    reset_in_progress = 1'b1;
    init_interfaces();
    wait_for_reset_safe_idle();

    fork
      begin
        @(posedge push_clk);
        push_rst <= 1'b1;
      end
      begin
        @(posedge pop_clk);
        pop_rst <= 1'b1;
      end
    join

    fork
      wait_push_cycles(ResetAssertPushCycles);
      wait_pop_cycles(ResetAssertPopCycles);
    join

    fork
      begin
        @(posedge push_clk);
        push_rst <= 1'b0;
      end
      begin
        @(posedge pop_clk);
        pop_rst <= 1'b0;
      end
    join

    wait_push_cycles(ResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    reset_seen = 1'b1;
    reset_in_progress = 1'b0;
  endtask

  task automatic reset_push_sender_with_pop_overlap();
    reset_in_progress = 1'b1;
    credit_sender_push_if.valid = 1'b0;
    credit_sender_push_if.data = '0;
    dut_pop_if.ready = 1'b0;
    push_credit_stall = 1'b0;
    credit_withhold_sender = '0;
    credit_withhold_push = '0;
    wait_for_reset_safe_idle();

    fork
      begin
        @(posedge push_clk);
        push_sender_rst <= 1'b1;
      end
      begin
        @(posedge pop_clk);
        pop_rst <= 1'b1;
      end
    join

    fork
      wait_push_cycles(SenderResetAssertPushCycles);
      wait_pop_cycles(ResetAssertPopCycles);
    join

    saw_push_sender_reset |= push_sender_in_reset_d;

    fork
      begin
        @(posedge push_clk);
        push_sender_rst <= 1'b0;
      end
      begin
        @(posedge pop_clk);
        pop_rst <= 1'b0;
      end
    join

    wait_push_cycles(SenderResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    reset_in_progress = 1'b0;
  endtask

  task automatic expect_push(input logic [Width-1:0] data);
    td.check(expected_count < Depth, "accepted push beyond FIFO depth");
    if (expected_count < Depth) begin
      expected_data.push_back(data);
      expected_count = expected_data.size();
    end
  endtask

  task automatic expect_pop(input logic [Width-1:0] data);
    logic [Width-1:0] expected;

    td.check(expected_data.size() > 0, "unexpected pop");
    if (expected_data.size() > 0) begin
      expected = expected_data.pop_front();
      td.check(data === expected, $sformatf(
               "pop data mismatch: got 0x%0h expected 0x%0h", data, expected));
      expected_count = expected_data.size();
    end
  endtask

  task automatic check_push_status_bounds(input string prefix);
    td.check(int'(dut_push_if.slots) <= Depth, {prefix, ": push_slots exceeded Depth"});
  endtask

  task automatic check_pop_status_bounds(input string prefix);
    td.check(int'(dut_pop_if.items) <= Depth, {prefix, ": pop_items exceeded Depth"});
  endtask

  task automatic check_quiescent_empty_status(input string prefix);
    wait_push_cycles(ResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    td.check_integer(expected_count, 0, {prefix, ": scoreboard should be empty"});
    td.check(dut_pop_if.empty, {prefix, ": FIFO should be empty"});
    td.check(!dut_pop_if.valid, {prefix, ": pop_valid should be low when empty"});
    td.check(!dut_push_if.full, {prefix, ": FIFO should not be full"});
    td.check_integer(int'(dut_pop_if.items), 0, {prefix, ": pop_items should be zero"});
    td.check_integer(int'(dut_push_if.slots), Depth, {prefix, ": push_slots should equal Depth"});
  endtask

  task automatic check_credit_status(input credit_check_status_t status);
    string prefix;

    prefix = credit_check_status_name(status);
    td.check(int'(credit_count_push) <= Depth, {prefix, ": DUT push credit count exceeded Depth"});
    td.check(int'(credit_count_sender) <= Depth, {prefix, ": sender credit count exceeded Depth"});
    td.check(int'(credit_available_push) <= Depth, {
             prefix, ": DUT available push credit exceeded Depth"});
  endtask

  task automatic monitor_push_credit_interface();
    saw_credit_backpressure |= credit_sender_push_if.valid && !credit_sender_push_if.ready;
    saw_credit_withhold |= |credit_withhold_push;
    saw_push_credit_stall |= push_credit_stall;
    saw_push_sender_reset |= push_sender_in_reset_d;
  endtask

  task automatic monitor_enable();
    fork
      forever begin
        @(posedge push_clk);
        if (!reset_in_progress && !push_rst) begin
          monitor_push_credit_interface();
          check_push_status_bounds("push_monitor");
          check_credit_status(CreditCheckPushMonitor);
        end
      end

      forever begin
        @(posedge pop_clk);
        if (!reset_in_progress && !pop_rst) begin
          check_pop_status_bounds("pop_monitor");
        end
      end
    join
  endtask

  task automatic push_timeout(input string message);
    wait_push_cycles(TimeoutPushCycles);
    $fatal(1, "%s", message);
  endtask

  task automatic pop_timeout(input string message);
    wait_pop_cycles(TimeoutPopCycles);
    $fatal(1, "%s", message);
  endtask

  task automatic wait_for_initial_credit();
    fork : wait_for_initial_credit_timeout_guard
      push_timeout("initial push credit timed out");
      begin
        while (credit_count_sender != credit_initial_push) begin
          @(posedge push_clk);
        end
      end
    join_any
    disable wait_for_initial_credit_timeout_guard;
  endtask

  task automatic drive_push(input logic [Width-1:0] data);
    fork : drive_push_timeout_guard
      push_timeout("push timed out");
      begin
        @(posedge push_clk);
        credit_sender_push_if.valid <= 1'b1;
        credit_sender_push_if.data  <= data;
        do begin
          @(posedge push_clk);
        end while (!credit_sender_push_if.ready);
        expect_push(data);
        credit_sender_push_if.valid <= 1'b0;
        credit_sender_push_if.data  <= '0;
      end
    join_any
    disable drive_push_timeout_guard;
  endtask

  task automatic drive_backpressured_push(input logic [Width-1:0] data);
    saw_credit_backpressure = 0;
    fork : drive_backpressured_push_timeout_guard
      push_timeout("backpressured push timed out");
      begin
        @(posedge push_clk);
        credit_sender_push_if.valid <= 1'b1;
        credit_sender_push_if.data  <= data;
        do begin
          @(posedge push_clk);
          saw_credit_backpressure |= !credit_sender_push_if.ready;
        end while (!credit_sender_push_if.ready);
        expect_push(data);
        credit_sender_push_if.valid <= 1'b0;
        credit_sender_push_if.data  <= '0;
      end
    join_any
    disable drive_backpressured_push_timeout_guard;

    td.check(saw_credit_backpressure, "push was not backpressured before acceptance");
  endtask

  task automatic drive_pop(output logic [Width-1:0] data);
    logic [Width-1:0] popped_data;

    fork : drive_pop_timeout_guard
      pop_timeout("pop timed out");
      begin
        @(posedge pop_clk);
        dut_pop_if.ready <= 1'b0;
        do @(posedge pop_clk); while (!dut_pop_if.valid);
        popped_data = dut_pop_if.data;
        dut_pop_if.ready <= 1'b1;
        @(posedge pop_clk);
        expect_pop(popped_data);
        dut_pop_if.ready <= 1'b0;
      end
    join_any
    disable drive_pop_timeout_guard;

    data = popped_data;
  endtask

  task automatic drive_ready_pop(output logic [Width-1:0] data);
    logic [Width-1:0] popped_data;

    fork : drive_ready_pop_timeout_guard
      pop_timeout("ready pop timed out");
      begin
        @(posedge pop_clk);
        dut_pop_if.ready <= 1'b1;
        do @(posedge pop_clk); while (!dut_pop_if.valid);
        popped_data = dut_pop_if.data;
        expect_pop(popped_data);
        @(posedge pop_clk);
        dut_pop_if.ready <= 1'b0;
      end
    join_any
    disable drive_ready_pop_timeout_guard;

    data = popped_data;
  endtask

  task automatic set_push_credit_stall(input logic stall);
    push_credit_stall = stall;
  endtask

  task automatic set_credit_withhold(input logic [CreditWidth-1:0] withhold);
    credit_withhold_push = withhold;
  endtask

  task automatic wait_for_pop_valid();
    fork : wait_for_pop_valid_timeout_guard
      pop_timeout("pop_valid timed out");
      begin
        while (!dut_pop_if.valid) begin
          @(posedge pop_clk);
        end
      end
    join_any
    disable wait_for_pop_valid_timeout_guard;
  endtask

  task automatic wait_for_push_no_credit();
    fork : wait_for_push_no_credit_timeout_guard
      push_timeout("push no-credit backpressure timed out");
      begin
        while (credit_sender_push_if.ready) begin
          @(posedge push_clk);
        end
        saw_credit_backpressure = 1'b1;
      end
    join_any
    disable wait_for_push_no_credit_timeout_guard;
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
    random_pushes_done = 1'b1;
  endtask

  task automatic drive_random_pops();
    logic [Width-1:0] data;
    int idle_cycles;

    while (!random_pushes_done || (expected_count > 0)) begin
      if (expected_count == 0) begin
        dut_pop_if.ready = 1'b0;
        wait_pop_cycles(1);
      end else begin
        idle_cycles = $urandom_range(RandomPopIdleMax, 0);
        wait_pop_cycles(idle_cycles);
        drive_pop(data);
      end
    end
  endtask

  task automatic test_idle();
    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();
    check_push_status_bounds("idle");
    check_pop_status_bounds("idle");
    check_credit_status(CreditCheckIdle);
  endtask

  task automatic test_credit_initialization();
    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();
    td.check_integer(int'(credit_count_sender), Depth, "sender initial credit mismatch");
    check_quiescent_empty_status("credit_initialization");
    check_credit_status(CreditCheckCreditInitialization);
  endtask

  task automatic test_empty_cutthrough();
    logic [Width-1:0] data;
    logic [Width-1:0] push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    push_data = Width'($urandom);
    fork
      drive_push(push_data);
      drive_ready_pop(data);
    join
    check_quiescent_empty_status("empty_cutthrough");
  endtask

  task automatic test_single_push_pop();
    logic [Width-1:0] data;
    logic [Width-1:0] push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    push_data = Width'($urandom);
    drive_push(push_data);
    drive_pop(data);
    check_quiescent_empty_status("single_push_pop");
  endtask

  task automatic test_fill_and_credit_backpressure();
    logic [Width-1:0] data;
    logic [Width-1:0] pending_push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    dut_pop_if.ready = 1'b0;
    for (int i = 0; i < Depth; i++) begin
      drive_push(Width'($urandom));
    end
    wait_for_push_no_credit();
    wait_push_cycles(PropDelay + 32'(RegisterPushOutputs) + 2);
    td.check(dut_push_if.full, "fill: FIFO should be full");
    td.check(!credit_sender_push_if.ready,
             "fill: push_ready should be low when sender has no credit");

    pending_push_data = Width'($urandom);
    fork
      drive_backpressured_push(pending_push_data);
      drive_pop(data);
    join

    drain_all();
    check_quiescent_empty_status("fill_and_credit_backpressure");
  endtask

  task automatic test_credit_withhold();
    logic [Width-1:0] data;
    logic [Width-1:0] push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    set_credit_withhold(CreditWidth'(1));
    push_data = Width'($urandom);
    drive_push(push_data);
    drive_pop(data);
    wait_push_cycles(2);
    td.check(saw_credit_withhold, "credit_withhold: monitor did not observe withhold");
    td.check(credit_count_sender < credit_initial_push,
             "credit_withhold: sender recovered withheld credit");

    set_credit_withhold('0);
    wait_for_initial_credit();
    check_quiescent_empty_status("credit_withhold");
  endtask

  task automatic test_push_credit_stall();
    logic [Width-1:0] data;
    logic [Width-1:0] push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    push_data = Width'($urandom);
    drive_push(push_data);
    set_push_credit_stall(1'b1);
    drive_pop(data);
    wait_push_cycles(2);
    td.check(saw_push_credit_stall, "push_credit_stall: monitor did not observe stall");
    td.check(credit_count_sender < credit_initial_push,
             "push_credit_stall: sender recovered stalled credit");

    set_push_credit_stall(1'b0);
    wait_for_initial_credit();
    check_quiescent_empty_status("push_credit_stall");
  endtask

  task automatic test_push_sender_reset();
    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    reset_push_sender_with_pop_overlap();
    td.check(saw_push_sender_reset, "push_sender_reset: DUT did not observe sender reset");
    wait_for_initial_credit();
    check_quiescent_empty_status("push_sender_reset");
  endtask

  task automatic test_pop_stall();
    logic [Width-1:0] stalled_data;
    logic [Width-1:0] data;
    logic [Width-1:0] push_data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    push_data = Width'($urandom);
    drive_push(push_data);
    wait_for_pop_valid();

    stalled_data = dut_pop_if.data;
    repeat (4) begin
      @(posedge pop_clk);
      td.check(dut_pop_if.valid, "pop_stall: pop_valid dropped while stalled");
      td.check(dut_pop_if.data === stalled_data, "pop_stall: pop_data changed while stalled");
    end

    drive_pop(data);
    check_quiescent_empty_status("pop_stall");
  endtask

  task automatic test_alternating();
    logic [Width-1:0] data;

    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    for (int i = 0; i < NumDirectedItems; i++) begin
      drive_push(Width'($urandom));
      drain_all();
    end
    check_quiescent_empty_status("alternating");
  endtask

  task automatic test_random();
    reset_scoreboard();
    init_interfaces();
    reset_dut();
    wait_for_initial_credit();

    fork : random_test_timeout_guard
      push_timeout("random test timed out");
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
    check_quiescent_empty_status("random");
  endtask

  task automatic run_all_tests();
    $display("Running test_idle");
    test_idle();
    $display("Running test_credit_initialization");
    test_credit_initialization();
    $display("Running test_empty_cutthrough");
    test_empty_cutthrough();
    $display("Running test_single_push_pop");
    test_single_push_pop();
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
    static br_cdc_pkg::cdc_delay_mode_t cdc_delay_mode = br_cdc_pkg::CdcDelayNone;
    void'($value$plusargs("cdc_delay_mode=%d", cdc_delay_mode));
    $display("set cdc_delay_mode = %0s", cdc_delay_mode.name());
`ifdef SIMULATION
    br_cdc_pkg::cdc_delay_mode = cdc_delay_mode;
`endif

    wait (clock_periods_configured);
    push_rst = 1'b1;
    pop_rst  = 1'b1;
    init_interfaces();
    reset_scoreboard();
    reset_in_progress = 1'b1;
    reset_seen = 1'b0;
    fork
      monitor_enable();
    join_none

    run_all_tests();

    init_interfaces();
    wait_push_cycles(ResetSettlePushCycles);
    wait_pop_cycles(ResetSettlePopCycles);
    td.check(expected_data.size() == 0, "final: scoreboard should be empty");
    check_credit_status(CreditCheckFinal);
    td.finish();
  end

endmodule
