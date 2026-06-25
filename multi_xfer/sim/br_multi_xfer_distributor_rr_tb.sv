// SPDX-License-Identifier: Apache-2.0

/*
 * Testbench for br_multi_xfer_distributor_rr. The DUT accepts a multi-transfer
 * push interface and distributes up to NumSymbols push payloads per cycle onto
 * NumFlows ready-valid pop flows using round-robin selection.
 *
 * Planned scenarios:
 * - Idle behavior after reset.
 * - Single-symbol distribution with all flows ready.
 * - Full-width NumSymbols distribution with all flows ready.
 * - More ready pop flows than sendable symbols, checking round-robin order.
 * - Fewer ready pop flows than sendable symbols, checking push backpressure.
 * - Sustained round-robin fairness across priority wraparound.
 * - Pop-flow stalls and per-flow independence.
 * - Push-data stability while push_sendable exceeds push_receivable.
 * - Bounded pseudo-random push_sendable/pop_ready traffic.
 */
module br_multi_xfer_distributor_rr_tb;

  // Parameters
  parameter int NumSymbols = 3;
  parameter int SymbolWidth = 8;
  parameter int NumFlows = 5;
  parameter bit EnableCoverPushBackpressure = 1;
  parameter bit EnableCoverMorePopReadyThanSendable = 1;
  parameter bit EnableAssertPushDataStability = 1;
  parameter bit EnableAssertFinalNotSendable = 1;
  parameter bit EnableAssertNoPushBackpressure = 0;
  parameter int NumRandomCycles = 120;

  localparam int CountWidth = $clog2(NumSymbols + 1);
  localparam int TimeoutCycles = 2000;

  // Clock and Reset
  logic clk;  // Testbench clock driven by br_test_driver.
  logic rst;  // Synchronous active-high reset driven by br_test_driver.

  // Multi-transfer push interface.
  logic [CountWidth-1:0] push_sendable;  // Number of valid push symbols offered this cycle.
  logic [CountWidth-1:0] push_receivable;  // Number of push symbols accepted by the DUT.
  logic [NumSymbols-1:0][SymbolWidth-1:0] push_data;  // Offered push payload symbols.

  // Ready-valid pop interfaces.
  logic [NumFlows-1:0] pop_valid;  // DUT valid output for each destination flow.
  logic [NumFlows-1:0] pop_ready;  // Testbench ready input for each destination flow.
  logic [NumFlows-1:0][SymbolWidth-1:0] pop_data;  // DUT payload output for each flow.

  // Scoreboard and monitor state.
  logic [NumFlows-1:0] expected_pop_valid;  // Per-flow expected pop validity for the sampled cycle.
  logic [NumFlows-1:0][SymbolWidth-1:0] expected_pop_data;  // Per-flow expected pop payload.
  int expected_count;  // Total expected pop handshakes remaining in the sampled cycle.
  int reference_next_flow;  // Expected next highest-priority flow in the RR model.
  logic [CountWidth-1:0] sampled_push_sendable;  // Push count sampled by the monitor.
  logic [CountWidth-1:0] sampled_push_receivable;  // Push accepted count sampled by the monitor.
  logic [NumSymbols-1:0][SymbolWidth-1:0] sampled_push_data;  // Push data sampled by the monitor.
  logic [NumFlows-1:0] sampled_pop_ready;  // Pop ready mask sampled by the monitor.
  logic [NumFlows-1:0] sampled_pop_fire;  // Pop handshakes sampled by the monitor.
  logic [NumFlows-1:0][SymbolWidth-1:0] sampled_pop_data;  // Pop data sampled by the monitor.
  logic [NumFlows-1:0] sampled_reference_grant;  // Expected grant mask for the sampled cycle.
  logic [SymbolWidth-1:0] pending_push_data[$];  // Source-side symbols not yet accepted.
  logic saw_push_backpressure;  // Sticky observation of push_sendable greater than push_receivable.
  logic saw_more_ready_than_sendable;  // Sticky observation of more ready flows than sendable data.
  logic saw_multi_flow_grant;  // Sticky observation of multiple pop flows granted in one cycle.
  logic saw_round_robin_wrap;  // Sticky observation that the RR priority wrapped past flow zero.
  logic monitor_done;  // Stop flag for the monitor thread.
  logic random_push_done;  // Stop flag indicating the random push source is fully drained.

  br_multi_xfer_distributor_rr #(
      .NumSymbols(NumSymbols),
      .SymbolWidth(SymbolWidth),
      .NumFlows(NumFlows),
      .EnableCoverPushBackpressure(EnableCoverPushBackpressure),
      .EnableCoverMorePopReadyThanSendable(EnableCoverMorePopReadyThanSendable),
      .EnableAssertPushDataStability(EnableAssertPushDataStability),
      .EnableAssertFinalNotSendable(EnableAssertFinalNotSendable),
      .EnableAssertNoPushBackpressure(EnableAssertNoPushBackpressure)
  ) dut (
      .clk,
      .rst,
      .push_sendable,
      .push_receivable,
      .push_data,
      .pop_valid,
      .pop_ready,
      .pop_data
  );

`ifdef DUMP_WAVES
  initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, br_multi_xfer_distributor_rr_tb);
  end
`endif

  br_test_driver td (
      .clk,
      .rst
  );

  function automatic int get_ready_count(input logic [NumFlows-1:0] ready_mask);
    // Intent: Count ready destination flows in a pop_ready-style mask.
    get_ready_count = 0;
    for (int i = 0; i < NumFlows; i++) begin
      get_ready_count += int'(ready_mask[i]);
    end
  endfunction

  function automatic logic [NumFlows-1:0] get_reference_grant_mask(
      input logic [NumFlows-1:0] ready_mask, input logic [CountWidth-1:0] sendable_count);
    // Intent: Return the expected RR-selected destination mask for one cycle.
    int grant_count;  // Number of destination flows selected so far.
    int flow_idx;  // Candidate destination flow in RR priority order.

    get_reference_grant_mask = '0;
    grant_count = 0;
    for (int offset = 0; offset < NumFlows; offset++) begin
      flow_idx = (reference_next_flow + offset) % NumFlows;
      if (ready_mask[flow_idx] && (grant_count < int'(sendable_count))) begin
        get_reference_grant_mask[flow_idx] = 1'b1;
        grant_count++;
      end
    end
  endfunction

  function automatic int map_grant_to_symbol_index(input int flow_idx,
                                                   input logic [NumFlows-1:0] grant_mask);
    // Intent: Map a granted flow to the corresponding push_data symbol index.
    int candidate_flow_idx;  // Candidate destination flow in RR priority order.

    map_grant_to_symbol_index = 0;
    for (int offset = 0; offset < NumFlows; offset++) begin
      candidate_flow_idx = (reference_next_flow + offset) % NumFlows;
      if (grant_mask[candidate_flow_idx]) begin
        if (candidate_flow_idx == flow_idx) begin
          return map_grant_to_symbol_index;
        end
        map_grant_to_symbol_index++;
      end
    end
  endfunction

  function automatic int get_reference_next_flow_after_grant(input logic [NumFlows-1:0] grant_mask);
    // Intent: Return the expected next highest-priority flow after a grant cycle.
    int candidate_flow_idx;  // Candidate destination flow in RR priority order.
    int last_grant_flow_idx;  // Lowest-priority flow granted in this cycle.

    get_reference_next_flow_after_grant = reference_next_flow;
    last_grant_flow_idx = -1;
    for (int offset = 0; offset < NumFlows; offset++) begin
      candidate_flow_idx = (reference_next_flow + offset) % NumFlows;
      if (grant_mask[candidate_flow_idx]) begin
        last_grant_flow_idx = candidate_flow_idx;
      end
    end
    if (last_grant_flow_idx >= 0) begin
      get_reference_next_flow_after_grant = (last_grant_flow_idx + 1) % NumFlows;
    end
  endfunction

  task automatic init_interfaces();
    // Intent: Drive push_sendable, push_data, and pop_ready to deterministic idle values.
    push_sendable = '0;
    push_data = '0;
    pop_ready = '0;
  endtask

  task automatic reset_scoreboard();
    // Intent: Clear sampled-cycle expectations, RR model state, and sticky monitor observations.
    pending_push_data.delete();
    expected_pop_valid = '0;
    expected_pop_data = '0;
    expected_count = 0;
    reference_next_flow = 0;
    sampled_push_sendable = '0;
    sampled_push_receivable = '0;
    sampled_push_data = '0;
    sampled_pop_ready = '0;
    sampled_pop_fire = '0;
    sampled_pop_data = '0;
    sampled_reference_grant = '0;
    saw_push_backpressure = 1'b0;
    saw_more_ready_than_sendable = 1'b0;
    saw_multi_flow_grant = 1'b0;
    saw_round_robin_wrap = 1'b0;
    random_push_done = 1'b0;
  endtask

  task automatic timeout(input int cycles, input string message);
    // Intent: Guard a concurrent operation with a bounded simulation-time error.
    td.wait_cycles(cycles);
    td.check(1'b0, message);
  endtask

  task automatic set_push_idle();
    // Intent: Deassert push_sendable and clear push_data after a directed push phase.
    push_sendable = '0;
    push_data = '0;
  endtask

  task automatic set_pop_ready_all(input logic ready);
    // Intent: Drive every pop flow ready input to the same value.
    pop_ready = {NumFlows{ready}};
  endtask

  task automatic set_pop_ready_mask(input logic [NumFlows-1:0] ready_mask);
    // Intent: Drive pop_ready from an explicit destination-flow mask.
    pop_ready = ready_mask;
  endtask

  task automatic set_push_payloads();
    // Intent: Fill push_data using direct $urandom calls for currently offered symbols.
    for (int i = 0; i < NumSymbols; i++) begin
      push_data[i] = SymbolWidth'($urandom);
    end
  endtask

  task automatic drive_push_cycle(input logic [CountWidth-1:0] sendable_count);
    // Intent: Drive one multi-transfer push cycle with a requested sendable count.
    @(negedge clk);
    push_sendable = sendable_count;
    set_push_payloads();
  endtask

  task automatic drive_pop_ready_cycle(input logic [NumFlows-1:0] ready_mask);
    // Intent: Drive one cycle of destination readiness without changing push stimulus.
    @(negedge clk);
    set_pop_ready_mask(ready_mask);
  endtask

  task automatic drive_cycle(input logic [CountWidth-1:0] sendable_count,
                             input logic [NumFlows-1:0] ready_mask);
    // Intent: Drive one combined push/pop cycle and allow monitors to sample the transfer.
    fork
      drive_push_cycle(sendable_count);
      drive_pop_ready_cycle(ready_mask);
    join
    td.wait_cycles();
  endtask

  task automatic wait_idle_cycles(input int cycles);
    // Intent: Advance with push idle while preserving or clearing pop readiness as needed.
    set_push_idle();
    set_pop_ready_all(1'b0);
    td.wait_cycles(cycles);
  endtask

  task automatic check_push_receivable();
    // Intent: Compare push_receivable against the reference number of granted flows.
    td.check_integer(int'(sampled_push_receivable), get_ready_count(sampled_reference_grant),
                     "push_receivable mismatch");
    td.check(int'(sampled_push_receivable) <= int'(sampled_push_sendable),
             "push_receivable exceeded push_sendable");
    td.check(int'(sampled_push_receivable) <= get_ready_count(sampled_pop_ready),
             "push_receivable exceeded ready flow count");
  endtask

  task automatic check_pop_outputs();
    // Intent: Compare pop_valid/pop_data against the reference grant mask and symbol mapping.
    int symbol_idx;  // Push symbol index expected on a granted pop flow.

    td.check(pop_valid === sampled_reference_grant, "pop_valid grant mask mismatch");
    for (int flow_idx = 0; flow_idx < NumFlows; flow_idx++) begin
      if (sampled_reference_grant[flow_idx]) begin
        symbol_idx = map_grant_to_symbol_index(flow_idx, sampled_reference_grant);
        td.check(pop_data[flow_idx] === sampled_push_data[symbol_idx], $sformatf(
                 "pop_data mismatch for flow %0d", flow_idx));
      end
    end
  endtask

  task automatic expect_push_distribution(input logic [CountWidth-1:0] sendable_count,
                                          input logic [NumSymbols-1:0][SymbolWidth-1:0] data,
                                          input logic [NumFlows-1:0] ready_mask);
    // Intent: Record expected per-flow payloads for the symbols accepted this cycle.
    logic [NumFlows-1:0] grant_mask;  // Expected destination flows selected this cycle.
    int symbol_idx;  // Push symbol index assigned to one granted destination flow.

    expected_pop_valid = '0;
    expected_pop_data = '0;
    expected_count = 0;
    grant_mask = get_reference_grant_mask(ready_mask, sendable_count);
    for (int flow_idx = 0; flow_idx < NumFlows; flow_idx++) begin
      if (grant_mask[flow_idx]) begin
        symbol_idx = map_grant_to_symbol_index(flow_idx, grant_mask);
        expected_pop_valid[flow_idx] = 1'b1;
        expected_pop_data[flow_idx] = data[symbol_idx];
        expected_count++;
      end
    end
  endtask

  task automatic expect_pop(input int flow_idx, input logic [SymbolWidth-1:0] data);
    // Intent: Check one accepted pop flow payload against the sampled-cycle expectation.
    td.check(expected_pop_valid[flow_idx], $sformatf("unexpected pop on flow %0d", flow_idx));
    if (expected_pop_valid[flow_idx]) begin
      expected_pop_valid[flow_idx] = 1'b0;
      expected_count--;
      td.check(data === expected_pop_data[flow_idx], $sformatf(
               "scoreboard pop mismatch on flow %0d", flow_idx));
    end
  endtask

  task automatic monitor_push_interface();
    // Intent: Sample push_sendable, push_receivable, push_data, and push-backpressure coverage.
    sampled_push_sendable = push_sendable;
    sampled_push_receivable = push_receivable;
    sampled_push_data = push_data;
    saw_push_backpressure |= push_sendable > push_receivable;
  endtask

  task automatic monitor_pop_interfaces();
    // Intent: Sample pop handshakes, pop payloads, and connect them to the scoreboard.
    sampled_pop_ready = pop_ready;
    sampled_pop_fire  = pop_valid & pop_ready;
    sampled_pop_data  = pop_data;
    saw_more_ready_than_sendable |= get_ready_count(pop_ready) > int'(push_sendable);
    saw_multi_flow_grant |= get_ready_count(sampled_pop_fire) > 1;

    for (int flow_idx = 0; flow_idx < NumFlows; flow_idx++) begin
      if (sampled_pop_fire[flow_idx]) begin
        expect_pop(flow_idx, sampled_pop_data[flow_idx]);
      end
    end
  endtask

  task automatic monitor_round_robin_state();
    // Intent: Update the reference RR priority state after sampled grant cycles.
    int next_flow;  // RR priority expected after the current sampled grants.

    next_flow = get_reference_next_flow_after_grant(sampled_reference_grant);
    saw_round_robin_wrap |= (next_flow < reference_next_flow) && (sampled_reference_grant != '0);
    reference_next_flow = next_flow;
  endtask

  task automatic monitor_enable();
    // Intent: Run push, pop, status, and RR monitors while the test sequence is active.
    while (!monitor_done) begin
      @(posedge clk);
      if (!rst) begin
        monitor_push_interface();
        sampled_pop_ready = pop_ready;
        sampled_reference_grant =
            get_reference_grant_mask(sampled_pop_ready, sampled_push_sendable);
        check_push_receivable();
        check_pop_outputs();
        expect_push_distribution(sampled_push_sendable, sampled_push_data, sampled_pop_ready);
        monitor_pop_interfaces();
        monitor_round_robin_state();
        td.check_integer(expected_count, 0, "zero-latency scoreboard did not drain in cycle");
      end
    end
  endtask

  task automatic drain_all();
    // Intent: Continue making all flows ready until all scoreboarded items have popped or timeout fires.
    fork : drain_timeout_guard
      timeout(TimeoutCycles, "drain timed out");
      begin
        do begin
          @(negedge clk);
          set_pop_ready_all(1'b1);
          if (pending_push_data.size() == 0) begin
            set_push_idle();
          end
        end while ((expected_count > 0) || (pending_push_data.size() > 0));
      end
    join_any
    disable drain_timeout_guard;

    @(negedge clk);
    set_push_idle();
    set_pop_ready_all(1'b0);
    td.wait_cycles();
  endtask

  task automatic retire_accepted_push_symbols();
    // Intent: Remove source-side symbols accepted on the previously sampled cycle.

    for (int i = 0; i < int'(sampled_push_receivable); i++) begin
      if (pending_push_data.size() > 0) begin
        void'(pending_push_data.pop_front());
      end
    end
  endtask

  task automatic enqueue_random_push_symbols(input int symbol_count);
    // Intent: Add direct-$urandom payloads to the independent push source queue.
    for (int i = 0; i < symbol_count; i++) begin
      pending_push_data.push_back(SymbolWidth'($urandom));
    end
  endtask

  task automatic drive_push_from_pending();
    // Intent: Drive the multi-transfer push interface from queued source payloads.
    int sendable_count;  // Number of pending source symbols offered this cycle.

    sendable_count = pending_push_data.size();
    if (sendable_count > NumSymbols) begin
      sendable_count = NumSymbols;
    end

    push_sendable = CountWidth'(sendable_count);
    push_data = '0;
    for (int i = 0; i < sendable_count; i++) begin
      push_data[i] = pending_push_data[i];
    end
  endtask

  task automatic drive_random_push_stream();
    // Intent: Drive an independent pseudo-random multi-transfer source stream.
    int new_symbol_count;  // Number of random source symbols added this cycle.

    random_push_done = 1'b0;
    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      @(negedge clk);
      retire_accepted_push_symbols();
      new_symbol_count = $urandom_range(NumSymbols, 0);
      enqueue_random_push_symbols(new_symbol_count);
      drive_push_from_pending();
    end

    fork : random_push_drain_timeout_guard
      timeout(TimeoutCycles, "random push source drain timed out");
      begin
        while (pending_push_data.size() > 0) begin
          @(negedge clk);
          retire_accepted_push_symbols();
          drive_push_from_pending();
        end
      end
    join_any
    disable random_push_drain_timeout_guard;

    @(negedge clk);
    retire_accepted_push_symbols();
    set_push_idle();
    random_push_done = 1'b1;
  endtask

  task automatic drive_random_pop_ready_stream();
    // Intent: Drive an independent pseudo-random pop-ready stream, then keep all flows ready to drain.
    logic [NumFlows-1:0] ready_mask;  // Random destination-flow ready mask for one cycle.

    for (int cycle = 0; cycle < NumRandomCycles; cycle++) begin
      @(negedge clk);
      for (int flow_idx = 0; flow_idx < NumFlows; flow_idx++) begin
        ready_mask[flow_idx] = $urandom_range(1, 0) != 0;
      end
      set_pop_ready_mask(ready_mask);
    end

    while (!random_push_done) begin
      @(negedge clk);
      set_pop_ready_all(1'b1);
    end
  endtask

  task automatic test_idle();
    // Intent: Verify reset and idle behavior with no sendable data and no ready flows.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    wait_idle_cycles(4);
  endtask

  task automatic test_single_symbol_all_ready();
    // Intent: Offer one symbol while all flows are ready and check first-priority routing.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    drive_cycle(CountWidth'(1), '1);
    wait_idle_cycles(1);
  endtask

  task automatic test_full_symbol_all_ready();
    // Intent: Offer NumSymbols symbols while all flows are ready and check ordered multi-grant routing.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    drive_cycle(CountWidth'(NumSymbols), '1);
    td.check(saw_multi_flow_grant, "multi-flow grant was not observed");
    wait_idle_cycles(1);
  endtask

  task automatic test_more_ready_than_sendable_rr();
    // Intent: Exercise more ready flows than sendable symbols and verify RR grant advancement.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    for (int i = 0; i < NumFlows + 2; i++) begin
      drive_cycle(CountWidth'(1), '1);
    end
    td.check(saw_more_ready_than_sendable, "more-ready-than-sendable scenario was not observed");
    td.check(saw_round_robin_wrap, "round-robin wrap was not observed");
    wait_idle_cycles(1);
  endtask

  task automatic test_fewer_ready_than_sendable_backpressure();
    // Intent: Exercise fewer ready flows than sendable symbols and observe push backpressure.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    fork
      begin
        @(negedge clk);
        push_sendable = CountWidth'(NumSymbols);
        set_push_payloads();
        td.wait_cycles();
        for (int i = 0; i < NumSymbols - 1; i++) begin
          push_data[i] = push_data[i+1];
        end
        push_sendable = CountWidth'(NumSymbols - 1);
        td.wait_cycles();
        set_push_idle();
      end
      begin
        @(negedge clk);
        set_pop_ready_mask(NumFlows'(1));
        td.wait_cycles();
        set_pop_ready_all(1'b1);
        td.wait_cycles();
        set_pop_ready_all(1'b0);
      end
    join

    td.check(saw_push_backpressure, "push backpressure was not observed");
    wait_idle_cycles(1);
  endtask

  task automatic test_round_robin_fairness();
    // Intent: Sustain all-ready traffic long enough to cover RR priority wraparound and fairness.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    for (int i = 0; i < NumFlows * 2; i++) begin
      drive_cycle(CountWidth'(1), '1);
    end
    td.check(saw_round_robin_wrap, "round-robin fairness test did not wrap priority");
    wait_idle_cycles(1);
  endtask

  task automatic test_pop_stalls();
    // Intent: Toggle ready masks to verify stalled flows do not receive unintended data.
    logic [NumFlows-1:0] ready_mask;  // One-hot ready mask rotated across destination flows.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    for (int flow_idx = 0; flow_idx < NumFlows; flow_idx++) begin
      ready_mask = '0;
      ready_mask[flow_idx] = 1'b1;
      drive_cycle(CountWidth'(1), ready_mask);
    end
    wait_idle_cycles(1);
  endtask

  task automatic test_push_data_stability_under_backpressure();
    // Intent: Hold excess push data stable while push_sendable exceeds push_receivable.
    int remaining_symbols;  // Number of source symbols still offered after each partial transfer.

    reset_scoreboard();
    init_interfaces();
    td.reset_dut();

    remaining_symbols = NumSymbols;
    @(negedge clk);
    push_sendable = CountWidth'(remaining_symbols);
    set_push_payloads();
    set_pop_ready_mask(NumFlows'(1));

    fork : push_data_stability_timeout_guard
      timeout(TimeoutCycles, "push data stability transfer timed out");
      begin
        while (remaining_symbols > 0) begin
          td.wait_cycles();
          remaining_symbols -= int'(sampled_push_receivable);
          for (int i = 0; i < remaining_symbols; i++) begin
            push_data[i] = push_data[i+int'(sampled_push_receivable)];
          end
          push_sendable = CountWidth'(remaining_symbols);
          set_pop_ready_mask(NumFlows'(1));
        end
      end
    join_any
    disable push_data_stability_timeout_guard;

    set_push_idle();
    set_pop_ready_all(1'b0);
    td.check(saw_push_backpressure, "push data stability test did not observe backpressure");
    wait_idle_cycles(1);
  endtask

  task automatic test_random();
    // Intent: Run bounded pseudo-random push_sendable and pop_ready masks using direct $urandom calls.
    reset_scoreboard();
    init_interfaces();
    td.reset_dut();
    fork
      drive_random_push_stream();
      drive_random_pop_ready_stream();
    join
    drain_all();
  endtask

  task automatic run_all_tests();
    // Intent: Sequence all directed scenarios, random traffic, final drain, and finish reporting.
    $display("Running test_idle");
    test_idle();
    $display("Running test_single_symbol_all_ready");
    test_single_symbol_all_ready();
    $display("Running test_full_symbol_all_ready");
    test_full_symbol_all_ready();
    $display("Running test_more_ready_than_sendable_rr");
    test_more_ready_than_sendable_rr();
    $display("Running test_fewer_ready_than_sendable_backpressure");
    test_fewer_ready_than_sendable_backpressure();
    $display("Running test_round_robin_fairness");
    test_round_robin_fairness();
    $display("Running test_pop_stalls");
    test_pop_stalls();
    $display("Running test_push_data_stability_under_backpressure");
    test_push_data_stability_under_backpressure();
    $display("Running test_random");
    test_random();
  endtask

  initial begin
    monitor_done = 1'b0;
    init_interfaces();
    reset_scoreboard();
    td.reset_dut();
    fork
      monitor_enable();
    join_none
    run_all_tests();
    @(negedge clk);
    set_push_idle();
    set_pop_ready_all(1'b0);
    td.wait_cycles(2);
    monitor_done = 1'b1;
    td.check_integer(expected_count, 0, "final scoreboard count mismatch");
    td.finish(5);
  end

endmodule : br_multi_xfer_distributor_rr_tb
