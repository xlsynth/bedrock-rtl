// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_sim_pkg::*;
import br_amba_apb_sim_pkg::*;
import br_amba_axil_sim_pkg::*;
import br_amba_axil_monitor_sim_pkg::*;
import br_amba_axil2apb_sim_pkg::*;

// Directed simulation testbench for br_amba_axil2apb.
//
// Stimulus plan:
// - reset/idle: reset the DUT and leave AXI-Lite/APB idle to check reset-visible outputs;
// - write/read no-delay: issue one transaction with AXI ready and APB PREADY available immediately;
// - zero-strobe write: issue a legal AXI-Lite write with WSTRB set to zero;
// - APB write/read PREADY backpressure: hold PREADY low during APB accesses across random counts;
// - write data skew: issue writes with AW before W;
// - write address skew: issue writes with W before AW;
// - read/write arbitration: present simultaneous read/write eligibility from reset and many
//   reads/writes with randomized data, strobes, and no intentional source delay;
// - AXI write response backpressure: delay BREADY across a random write transaction count;
// - AXI read response backpressure: delay RREADY across a random read transaction count;
// - mixed AXI response backpressure: delay BREADY/RREADY with interleaved reads and writes;
// - error propagation: complete APB writes and reads with PSLVERR set across many transfers;
// - mixed directed sequence: run reads and writes with representative gaps and wait states;
// - stress: run sustained traffic with no intentional stalls on either side;
// - mid-transaction reset: assert reset after a partial AXI write, during APB setup/access, and
//   while AXI responses are pending; then reinitialize and run traffic.
module br_amba_axil2apb_tb;
  parameter int AddrWidth = 12;
  parameter int DataWidth = 32;

  localparam int StrbWidth = DataWidth / 8;
  localparam int ResetCycles = 5;
  localparam int ClockPeriodNs = 10;
  localparam int TimeoutCycles = 5000;
  localparam int MidResetTimeoutCycles = 64;
  localparam int NoWrites = 0;
  localparam int NoReads = 0;
  localparam int SingleWrite = 1;
  localparam int SingleRead = 1;
  localparam int NoGapCycles = 0;
  localparam int NoStallCycles = 0;
  localparam int ChannelSkewCycles = 3;
  localparam int ApbBackpressureWaitCycles = 3;
  localparam int ResponseStallCycles = 3;
  localparam int MixedAwGapCycles = 1;
  localparam int MixedWGapCycles = 2;
  localparam int MixedArGapCycles = 1;
  localparam int MixedApbWaitCycles = 1;
  localparam int MidResetWriteDataDelayCycles = 8;
  localparam int MidResetResponseStallCycles = 16;
  localparam int MidResetRecoveryWaitCycles = 5;
  localparam int MinDirectedTransactions = 20;
  localparam int MaxDirectedTransactions = 40;
  localparam int MinStressTransactions = 128;
  localparam int MaxStressTransactions = 192;
  localparam logic [StrbWidth-1:0] ZeroStrobe = '0;
  localparam logic [StrbWidth-1:0] MidResetStrobe = '1;

  logic clk;
  logic rst;
  logic axil_driver_failed;
  logic apb_completer_failed;
  logic apb_monitor_failed;
  logic axil_monitor_failed;
  logic scoreboard_failed;
  logic timeout_failed;
  event timeout_tick;

  // AXI4-Lite manager-side signals.
  logic [AddrWidth-1:0] awaddr;
  logic [AxiProtWidth-1:0] awprot;
  logic awvalid;
  logic awready;
  logic [DataWidth-1:0] wdata;
  logic [StrbWidth-1:0] wstrb;
  logic wvalid;
  logic wready;
  logic [AxiRespWidth-1:0] bresp;
  logic bvalid;
  logic bready;
  logic [AddrWidth-1:0] araddr;
  logic [AxiProtWidth-1:0] arprot;
  logic arvalid;
  logic arready;
  logic [DataWidth-1:0] rdata;
  logic [AxiRespWidth-1:0] rresp;
  logic rvalid;
  logic rready;

  // APB completer-side signals.
  logic [AddrWidth-1:0] paddr;
  logic psel;
  logic penable;
  logic [ApbProtWidth-1:0] pprot;
  logic [StrbWidth-1:0] pstrb;
  logic pwrite;
  logic [DataWidth-1:0] pwdata;
  logic [DataWidth-1:0] prdata;
  logic pready;
  logic pslverr;

  always @(posedge clk) begin
    ->timeout_tick;
  end

  clocking cb @(posedge clk);
    default input #1step;
    input awvalid;
    input awready;
    input psel;
    input penable;
    input bvalid;
    input rvalid;
  endclocking

  br_test_driver #(
      .ResetCycles  (ResetCycles),
      .ClockPeriodNs(ClockPeriodNs)
  ) td (
      .clk(clk),
      .rst(rst)
  );

  br_amba_axil2apb #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth)
  ) dut (
      .clk(clk),
      .rst(rst),
      .awaddr(awaddr),
      .awprot(awprot),
      .awvalid(awvalid),
      .awready(awready),
      .wdata(wdata),
      .wstrb(wstrb),
      .wvalid(wvalid),
      .wready(wready),
      .bresp(bresp),
      .bvalid(bvalid),
      .bready(bready),
      .araddr(araddr),
      .arprot(arprot),
      .arvalid(arvalid),
      .arready(arready),
      .rdata(rdata),
      .rresp(rresp),
      .rvalid(rvalid),
      .rready(rready),
      .paddr(paddr),
      .psel(psel),
      .penable(penable),
      .pprot(pprot),
      .pstrb(pstrb),
      .pwrite(pwrite),
      .pwdata(pwdata),
      .prdata(prdata),
      .pready(pready),
      .pslverr(pslverr)
  );

  br_amba_axil_requester_driver #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axil_driver (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(awaddr),
      .axil_awprot(awprot),
      .axil_awvalid(awvalid),
      .axil_awready(awready),
      .axil_wdata(wdata),
      .axil_wstrb(wstrb),
      .axil_wvalid(wvalid),
      .axil_wready(wready),
      .axil_bvalid(bvalid),
      .axil_bready(bready),
      .axil_araddr(araddr),
      .axil_arprot(arprot),
      .axil_arvalid(arvalid),
      .axil_arready(arready),
      .axil_rvalid(rvalid),
      .axil_rready(rready),
      .failed(axil_driver_failed)
  );

  br_amba_apb_completer_driver #(
      .DataWidth(DataWidth),
      .TimeoutCycles(TimeoutCycles)
  ) apb_completer (
      .clk(clk),
      .target_psel(psel),
      .target_penable(penable),
      .pready(pready),
      .prdata(prdata),
      .pslverr(pslverr),
      .failed(apb_completer_failed)
  );

  br_amba_apb_monitor #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth)
  ) apb_monitor (
      .clk(clk),
      .rst(rst),
      .paddr(paddr),
      .psel(psel),
      .penable(penable),
      .pprot(pprot),
      .pstrb(pstrb),
      .pwrite(pwrite),
      .pwdata(pwdata),
      .prdata(prdata),
      .pready(pready),
      .pslverr(pslverr),
      .failed(apb_monitor_failed)
  );

  br_amba_axil_monitor #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth)
  ) axil_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(awaddr),
      .axil_awprot(awprot),
      .axil_awuser('0),
      .axil_awvalid(awvalid),
      .axil_awready(awready),
      .axil_wdata(wdata),
      .axil_wstrb(wstrb),
      .axil_wuser('0),
      .axil_wvalid(wvalid),
      .axil_wready(wready),
      .axil_bresp(bresp),
      .axil_buser('0),
      .axil_bvalid(bvalid),
      .axil_bready(bready),
      .axil_araddr(araddr),
      .axil_arprot(arprot),
      .axil_aruser('0),
      .axil_arvalid(arvalid),
      .axil_arready(arready),
      .axil_rdata(rdata),
      .axil_rresp(rresp),
      .axil_ruser('0),
      .axil_rvalid(rvalid),
      .axil_rready(rready),
      .failed(axil_monitor_failed)
  );

  br_amba_axil2apb_scoreboard #(
      .DataWidth(DataWidth),
      .ClockPeriodNs(ClockPeriodNs)
  ) scoreboard (
      .failed(scoreboard_failed)
  );

  function automatic int directed_transaction_count();
    directed_transaction_count = $urandom_range(MaxDirectedTransactions, MinDirectedTransactions);
  endfunction

  function automatic int stress_transaction_count();
    stress_transaction_count = $urandom_range(MaxStressTransactions, MinStressTransactions);
  endfunction

  function automatic apb_response_t random_response(input logic allow_slverr,
                                                    input logic force_slverr);
    random_response.ready = Pready1;
    random_response.rdata = ApbDataWidth'(DataWidth'(get_random_bits(DataWidth)));
    random_response.slverr = force_slverr ?
        Pslverr1 : (allow_slverr ? logic'($urandom_range(1, 0)) : Pslverr0);
  endfunction

  function automatic logic [StrbWidth-1:0] random_write_strobe();
    random_write_strobe = StrbWidth'(get_random_bits(StrbWidth));
  endfunction

  task automatic init_scenario(output axil2apb_scenario_t scenario, input int num_writes,
                               input int num_reads);
    scenario.num_writes = num_writes;
    scenario.num_reads = num_reads;
    scenario.min_aw_gap_cycles = NoGapCycles;
    scenario.max_aw_gap_cycles = NoGapCycles;
    scenario.min_w_gap_cycles = NoGapCycles;
    scenario.max_w_gap_cycles = NoGapCycles;
    scenario.min_ar_gap_cycles = NoGapCycles;
    scenario.max_ar_gap_cycles = NoGapCycles;
    scenario.min_b_stall_cycles = NoStallCycles;
    scenario.max_b_stall_cycles = NoStallCycles;
    scenario.min_r_stall_cycles = NoStallCycles;
    scenario.max_r_stall_cycles = NoStallCycles;
    scenario.apb_wait_cycles = NoStallCycles;
    scenario.allow_slverr = 1'b0;
    scenario.force_slverr = 1'b0;
  endtask

  task automatic check_helpers(input string scenario_name);
    string axil_driver_message = $sformatf(
        "%s: AXI-Lite requester driver reported failures", scenario_name
    );
    string apb_completer_message = $sformatf(
        "%s: APB completer driver reported failures", scenario_name
    );
    string apb_monitor_message = $sformatf("%s: APB monitor reported failures", scenario_name);
    string axil_monitor_message = $sformatf(
        "%s: AXI-Lite monitor reported failures", scenario_name
    );
    string scoreboard_message = $sformatf("%s: scoreboard reported failures", scenario_name);
    string timeout_message = $sformatf("%s: timeout reported failures", scenario_name);

    td.check(!axil_driver_failed, axil_driver_message);
    td.check(!apb_completer_failed, apb_completer_message);
    td.check(!apb_monitor_failed, apb_monitor_message);
    td.check(!axil_monitor_failed, axil_monitor_message);
    td.check(!scoreboard_failed, scoreboard_message);
    td.check(!timeout_failed, timeout_message);
  endtask

  task automatic init_idle();
    axil_driver.init_idle();
    apb_completer.init_idle();
    apb_monitor.init_idle();
    axil_monitor.init_idle();
    scoreboard.init_idle();
    timeout_failed = 1'b0;
  endtask

  task automatic queue_random_write_with_strobe(input axil2apb_scenario_t scenario,
                                                input logic [StrbWidth-1:0] strb,
                                                output apb_response_t response);
    logic [AddrWidth-1:0] addr = AddrWidth'($urandom());
    logic [AxiProtWidth-1:0] prot = AxiProtWidth'($urandom());
    logic [DataWidth-1:0] data = DataWidth'(get_random_bits(DataWidth));
    int aw_gap_cycles = $urandom_range(scenario.max_aw_gap_cycles, scenario.min_aw_gap_cycles);
    int w_gap_cycles = $urandom_range(scenario.max_w_gap_cycles, scenario.min_w_gap_cycles);
    int b_stall_cycles = $urandom_range(scenario.max_b_stall_cycles, scenario.min_b_stall_cycles);

    response = random_response(scenario.allow_slverr, scenario.force_slverr);
    axil_driver.queue_write(addr, prot, data, strb, aw_gap_cycles, w_gap_cycles, b_stall_cycles);
  endtask

  task automatic queue_random_write(input axil2apb_scenario_t scenario,
                                    output apb_response_t response);
    queue_random_write_with_strobe(scenario, random_write_strobe(), response);
  endtask

  task automatic queue_random_read(input axil2apb_scenario_t scenario,
                                   output apb_response_t response);
    logic [AddrWidth-1:0] addr = AddrWidth'($urandom());
    logic [AxiProtWidth-1:0] prot = AxiProtWidth'($urandom());
    int ar_gap_cycles = $urandom_range(scenario.max_ar_gap_cycles, scenario.min_ar_gap_cycles);
    int r_stall_cycles = $urandom_range(scenario.max_r_stall_cycles, scenario.min_r_stall_cycles);

    response = random_response(scenario.allow_slverr, scenario.force_slverr);
    axil_driver.queue_read(addr, prot, ar_gap_cycles, r_stall_cycles);
  endtask

  task automatic queue_writes(input axil2apb_scenario_t scenario,
                              ref apb_response_t response_queue[$]);
    check_scenario_cycle_ranges(scenario);
    for (int i = 0; i < scenario.num_writes; i++) begin
      apb_response_t response;

      queue_random_write(scenario, response);
      response_queue.push_back(response);
    end
  endtask

  task automatic queue_reads(input axil2apb_scenario_t scenario,
                             ref apb_response_t response_queue[$]);
    check_scenario_cycle_ranges(scenario);
    for (int i = 0; i < scenario.num_reads; i++) begin
      apb_response_t response;

      queue_random_read(scenario, response);
      response_queue.push_back(response);
    end
  endtask

  // Responses are queued in the same order as the stimulus is queued. The
  // scoreboard predicts which accepted AXI-Lite request consumes each APB
  // response from observed request timestamps.
  task automatic queue_mixed_transactions(input axil2apb_scenario_t scenario,
                                          ref apb_response_t response_queue[$]);
    int max_transaction_count;

    check_scenario_cycle_ranges(scenario);
    max_transaction_count = scenario.num_writes > scenario.num_reads ? scenario.num_writes :
                                                                                 scenario.num_reads;
    for (int i = 0; i < max_transaction_count; i++) begin
      apb_response_t response;

      if (i < scenario.num_reads) begin
        queue_random_read(scenario, response);
        response_queue.push_back(response);
      end
      if (i < scenario.num_writes) begin
        queue_random_write(scenario, response);
        response_queue.push_back(response);
      end
    end
  endtask

  task automatic check_scenario_cycle_ranges(input axil2apb_scenario_t scenario);
    td.check(scenario.min_aw_gap_cycles >= 0, "AXI-Lite AW gap min cycles is negative");
    td.check(scenario.max_aw_gap_cycles >= 0, "AXI-Lite AW gap max cycles is negative");
    td.check(scenario.max_aw_gap_cycles >= scenario.min_aw_gap_cycles,
             "AXI-Lite AW gap max cycles is less than min cycles");
    td.check(scenario.min_w_gap_cycles >= 0, "AXI-Lite W gap min cycles is negative");
    td.check(scenario.max_w_gap_cycles >= 0, "AXI-Lite W gap max cycles is negative");
    td.check(scenario.max_w_gap_cycles >= scenario.min_w_gap_cycles,
             "AXI-Lite W gap max cycles is less than min cycles");
    td.check(scenario.min_ar_gap_cycles >= 0, "AXI-Lite AR gap min cycles is negative");
    td.check(scenario.max_ar_gap_cycles >= 0, "AXI-Lite AR gap max cycles is negative");
    td.check(scenario.max_ar_gap_cycles >= scenario.min_ar_gap_cycles,
             "AXI-Lite AR gap max cycles is less than min cycles");
    td.check(scenario.min_b_stall_cycles >= 0, "AXI-Lite B stall min cycles is negative");
    td.check(scenario.max_b_stall_cycles >= 0, "AXI-Lite B stall max cycles is negative");
    td.check(scenario.max_b_stall_cycles >= scenario.min_b_stall_cycles,
             "AXI-Lite B stall max cycles is less than min cycles");
    td.check(scenario.min_r_stall_cycles >= 0, "AXI-Lite R stall min cycles is negative");
    td.check(scenario.max_r_stall_cycles >= 0, "AXI-Lite R stall max cycles is negative");
    td.check(scenario.max_r_stall_cycles >= scenario.min_r_stall_cycles,
             "AXI-Lite R stall max cycles is less than min cycles");
    td.check(scenario.apb_wait_cycles >= 0, "APB wait cycles is negative");
  endtask

  task automatic check_observed_request_counts(input axil2apb_scenario_t scenario,
                                               input axil_aw_observation_t observed_aw_queue[$],
                                               input axil_w_observation_t observed_w_queue[$],
                                               input axil_ar_observation_t observed_ar_queue[$]);
    td.check(observed_aw_queue.size() == scenario.num_writes, $sformatf(
             "Observed AW request count mismatch: expected %0d observed %0d",
             scenario.num_writes,
             observed_aw_queue.size()
             ));
    td.check(observed_w_queue.size() == scenario.num_writes, $sformatf(
             "Observed W request count mismatch: expected %0d observed %0d",
             scenario.num_writes,
             observed_w_queue.size()
             ));
    td.check(observed_ar_queue.size() == scenario.num_reads, $sformatf(
             "Observed AR request count mismatch: expected %0d observed %0d",
             scenario.num_reads,
             observed_ar_queue.size()
             ));
  endtask

  // Runs queued AXI stimulus, APB response driving, protocol monitors, and the
  // bridge scoreboard as one scenario-level unit.
  task automatic run_queued_scenario(input string scenario_name, input axil2apb_scenario_t scenario,
                                     input apb_response_t response_queue[$]);
    apb_response_controls_t response_controls;
    axil_request_state_observation_t observed_request_state_queue[$];
    apb_transfer_observation_t observed_apb_queue[$];
    axil_aw_observation_t observed_aw_queue[$];
    axil_w_observation_t observed_w_queue[$];
    axil_b_observation_t observed_b_queue[$];
    axil_ar_observation_t observed_ar_queue[$];
    axil_r_observation_t observed_r_queue[$];

    response_controls.num_transactions = scenario.num_writes + scenario.num_reads;
    response_controls.wait_cycles = scenario.apb_wait_cycles;
    td.check(response_queue.size() == response_controls.num_transactions, $sformatf(
             "Response queue size mismatch: expected %0d observed %0d",
             response_controls.num_transactions,
             response_queue.size()
             ));

    // Each scenario is self-contained. Resetting here keeps bridge arbitration
    // state from leaking between directed tests and changing the expected
    // read/write ordering.
    td.reset_dut();

    fork
      begin
        fork
          axil_driver.run(scenario.num_writes, scenario.num_reads);
          apb_completer.run_queue(response_queue, response_controls);
        join
      end
      apb_monitor.run();
      axil_monitor.run();
      timeout(timeout_tick, TimeoutCycles, $sformatf(
              "%s: timeout waiting for br_amba_axil2apb scenario completion", scenario_name),
              timeout_failed);
    join_any
    disable fork;

    apb_monitor.get_observed_transfers(observed_apb_queue);
    axil_monitor.get_observed_request_state_observations(observed_request_state_queue);
    axil_monitor.get_observed_request_observations(observed_aw_queue, observed_w_queue,
                                                   observed_ar_queue);
    axil_monitor.get_observed_response_observations(observed_b_queue, observed_r_queue);
    check_observed_request_counts(scenario, observed_aw_queue, observed_w_queue, observed_ar_queue);
    scoreboard.compare(observed_request_state_queue, observed_aw_queue, observed_w_queue,
                       observed_ar_queue, response_queue, observed_apb_queue, observed_b_queue,
                       observed_r_queue);
    check_helpers(scenario_name);
  endtask

  task automatic test_reset_idle();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, NoWrites, NoReads);
    init_idle();
    run_queued_scenario("reset idle", scenario, response_queue);
    td.check(!psel, "PSEL asserted while idle after reset");
    td.check(!penable, "PENABLE asserted while idle after reset");
    td.check(!bvalid, "BVALID asserted while idle after reset");
    td.check(!rvalid, "RVALID asserted while idle after reset");
  endtask

  task automatic test_write_no_delay();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, SingleWrite, NoReads);
    init_idle();
    queue_writes(scenario, response_queue);
    run_queued_scenario("write no delay", scenario, response_queue);
  endtask

  task automatic test_read_no_delay();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, NoWrites, SingleRead);
    init_idle();
    queue_reads(scenario, response_queue);
    run_queued_scenario("read no delay", scenario, response_queue);
  endtask

  task automatic test_zero_strobe_write();
    axil2apb_scenario_t scenario;
    apb_response_t response;
    apb_response_t response_queue[$];

    init_scenario(scenario, SingleWrite, NoReads);
    init_idle();
    queue_random_write_with_strobe(scenario, ZeroStrobe, response);
    response_queue.push_back(response);
    run_queued_scenario("zero strobe write", scenario, response_queue);
  endtask

  task automatic test_apb_pready_write_backpressure();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), NoReads);
    scenario.apb_wait_cycles = ApbBackpressureWaitCycles;
    init_idle();
    queue_writes(scenario, response_queue);
    run_queued_scenario("APB PREADY write backpressure", scenario, response_queue);
  endtask

  task automatic test_apb_pready_read_backpressure();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, NoWrites, directed_transaction_count());
    scenario.apb_wait_cycles = ApbBackpressureWaitCycles;
    init_idle();
    queue_reads(scenario, response_queue);
    run_queued_scenario("APB PREADY read backpressure", scenario, response_queue);
  endtask

  task automatic test_write_data_skew();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), NoReads);
    scenario.min_w_gap_cycles = ChannelSkewCycles;
    scenario.max_w_gap_cycles = ChannelSkewCycles;
    init_idle();
    queue_writes(scenario, response_queue);
    run_queued_scenario("write data skew", scenario, response_queue);
  endtask

  task automatic test_write_address_skew();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), NoReads);
    scenario.min_aw_gap_cycles = ChannelSkewCycles;
    scenario.max_aw_gap_cycles = ChannelSkewCycles;
    init_idle();
    queue_writes(scenario, response_queue);
    run_queued_scenario("write address skew", scenario, response_queue);
  endtask

  task automatic test_read_write_arbitration();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), directed_transaction_count());
    init_idle();
    queue_mixed_transactions(scenario, response_queue);
    run_queued_scenario("read/write arbitration", scenario, response_queue);
  endtask

  task automatic test_axi_write_response_backpressure();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), NoReads);
    scenario.max_b_stall_cycles = ResponseStallCycles;
    init_idle();
    queue_writes(scenario, response_queue);
    run_queued_scenario("AXI write response backpressure", scenario, response_queue);
  endtask

  task automatic test_axi_read_response_backpressure();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, NoWrites, directed_transaction_count());
    scenario.max_r_stall_cycles = ResponseStallCycles;
    init_idle();
    queue_reads(scenario, response_queue);
    run_queued_scenario("AXI read response backpressure", scenario, response_queue);
  endtask

  task automatic test_mixed_response_backpressure();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), directed_transaction_count());
    scenario.min_b_stall_cycles = ResponseStallCycles;
    scenario.max_b_stall_cycles = ResponseStallCycles;
    scenario.min_r_stall_cycles = ResponseStallCycles;
    scenario.max_r_stall_cycles = ResponseStallCycles;
    init_idle();
    queue_mixed_transactions(scenario, response_queue);
    run_queued_scenario("mixed AXI response backpressure", scenario, response_queue);
  endtask

  task automatic test_error_response_propagation();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), directed_transaction_count());
    scenario.force_slverr = 1'b1;

    init_idle();
    queue_mixed_transactions(scenario, response_queue);
    run_queued_scenario("error response propagation", scenario, response_queue);
  endtask

  task automatic test_mixed_directed_sequence();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, directed_transaction_count(), directed_transaction_count());
    scenario.max_aw_gap_cycles = MixedAwGapCycles;
    scenario.max_w_gap_cycles  = MixedWGapCycles;
    scenario.max_ar_gap_cycles = MixedArGapCycles;
    scenario.apb_wait_cycles   = MixedApbWaitCycles;

    init_idle();
    queue_mixed_transactions(scenario, response_queue);
    run_queued_scenario("mixed directed sequence", scenario, response_queue);
  endtask

  task automatic test_stress();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    init_scenario(scenario, stress_transaction_count(), stress_transaction_count());
    scenario.allow_slverr = 1'b1;
    init_idle();
    queue_mixed_transactions(scenario, response_queue);
    run_queued_scenario("stress", scenario, response_queue);
  endtask

  task automatic check_mid_reset_abort(input string scenario_name, input int expected_apb_transfers,
                                       input logic expected_apb_request_seen);
    apb_transfer_observation_t aborted_apb_queue[$];
    logic aborted_apb_request_seen;
    axil_b_observation_t aborted_b_queue[$];
    axil_r_observation_t aborted_r_queue[$];

    apb_monitor.get_observed_transfers(aborted_apb_queue);
    aborted_apb_request_seen = apb_monitor.saw_request_phase();
    axil_monitor.get_observed_response_observations(aborted_b_queue, aborted_r_queue);
    td.check(aborted_apb_request_seen == expected_apb_request_seen, $sformatf(
             "%s: APB request phase visibility mismatch", scenario_name));
    td.check(aborted_apb_queue.size() == expected_apb_transfers, $sformatf(
             "%s: APB transfer count mismatch before reset", scenario_name));
    td.check(aborted_b_queue.size() == 0, $sformatf(
             "%s: AXI-Lite B response observed across reset", scenario_name));
    td.check(aborted_r_queue.size() == 0, $sformatf(
             "%s: AXI-Lite R response observed across reset", scenario_name));
    check_helpers(scenario_name);
  endtask

  task automatic check_mid_reset_recovery(input string scenario_name);
    init_idle();
    td.wait_cycles(MidResetRecoveryWaitCycles);
    td.check(!psel, $sformatf(
             "%s: PSEL asserted after mid-transaction reset recovery", scenario_name));
    td.check(!penable, $sformatf(
             "%s: PENABLE asserted after mid-transaction reset recovery", scenario_name));
    td.check(!bvalid, $sformatf(
             "%s: BVALID asserted after mid-transaction reset recovery", scenario_name));
    td.check(!rvalid, $sformatf(
             "%s: RVALID asserted after mid-transaction reset recovery", scenario_name));
  endtask

  task automatic reset_after_incomplete_write();
    init_idle();
    axil_driver.queue_write(AddrWidth'($urandom()), AxiProtWidth'($urandom()),
                            DataWidth'(get_random_bits(DataWidth)), MidResetStrobe, NoGapCycles,
                            MidResetWriteDataDelayCycles, NoStallCycles);
    fork
      begin
        fork
          axil_driver.run(SingleWrite, NoReads);
          apb_monitor.run();
          axil_monitor.run();
        join
      end
      begin
        @cb;
        while (!(cb.awvalid && cb.awready)) @cb;
        td.reset_dut();
      end
      timeout(timeout_tick, MidResetTimeoutCycles,
              "Timeout waiting for br_amba_axil2apb mid-transaction reset scenario",
              timeout_failed);
    join_any
    disable fork;

    check_mid_reset_abort("reset after incomplete AXI-Lite write", 0, 1'b0);
    check_mid_reset_recovery("reset after incomplete AXI-Lite write");
  endtask

  task automatic reset_during_apb_setup();
    init_idle();
    axil_driver.queue_write(AddrWidth'($urandom()), AxiProtWidth'($urandom()),
                            DataWidth'(get_random_bits(DataWidth)), MidResetStrobe, NoGapCycles,
                            NoGapCycles, NoStallCycles);
    fork
      begin
        fork
          axil_driver.run(SingleWrite, NoReads);
          apb_monitor.run();
          axil_monitor.run();
        join
      end
      begin
        @cb;
        while (!(cb.psel && !cb.penable)) @cb;
        td.reset_dut();
      end
      timeout(timeout_tick, MidResetTimeoutCycles,
              "Timeout waiting to reset br_amba_axil2apb during APB setup", timeout_failed);
    join_any
    disable fork;

    check_mid_reset_abort("reset during APB setup", 0, 1'b1);
    check_mid_reset_recovery("reset during APB setup");
  endtask

  task automatic reset_during_apb_access();
    init_idle();
    axil_driver.queue_write(AddrWidth'($urandom()), AxiProtWidth'($urandom()),
                            DataWidth'(get_random_bits(DataWidth)), MidResetStrobe, NoGapCycles,
                            NoGapCycles, NoStallCycles);
    fork
      begin
        fork
          axil_driver.run(SingleWrite, NoReads);
          apb_monitor.run();
          axil_monitor.run();
        join
      end
      begin
        @cb;
        while (!(cb.psel && cb.penable)) @cb;
        td.reset_dut();
      end
      timeout(timeout_tick, MidResetTimeoutCycles,
              "Timeout waiting to reset br_amba_axil2apb during APB access", timeout_failed);
    join_any
    disable fork;

    check_mid_reset_abort("reset during APB access", 0, 1'b1);
    check_mid_reset_recovery("reset during APB access");
  endtask

  task automatic reset_during_write_response();
    apb_response_controls_t response_controls;
    apb_response_t response_queue[$];

    init_idle();
    response_queue.push_back(random_response(1'b0, 1'b0));
    response_controls.num_transactions = SingleWrite;
    response_controls.wait_cycles = NoStallCycles;
    axil_driver.queue_write(AddrWidth'($urandom()), AxiProtWidth'($urandom()),
                            DataWidth'(get_random_bits(DataWidth)), MidResetStrobe, NoGapCycles,
                            NoGapCycles, MidResetResponseStallCycles);
    fork
      begin
        fork
          axil_driver.run(SingleWrite, NoReads);
          apb_completer.run_queue(response_queue, response_controls);
          apb_monitor.run();
          axil_monitor.run();
        join
      end
      begin
        @cb;
        while (!cb.bvalid) @cb;
        td.reset_dut();
      end
      timeout(timeout_tick, MidResetTimeoutCycles,
              "Timeout waiting to reset br_amba_axil2apb during write response", timeout_failed);
    join_any
    disable fork;

    check_mid_reset_abort("reset during AXI-Lite write response", 1, 1'b1);
    check_mid_reset_recovery("reset during AXI-Lite write response");
  endtask

  task automatic reset_during_read_response();
    apb_response_controls_t response_controls;
    apb_response_t response_queue[$];

    init_idle();
    response_queue.push_back(random_response(1'b0, 1'b0));
    response_controls.num_transactions = SingleRead;
    response_controls.wait_cycles = NoStallCycles;
    axil_driver.queue_read(AddrWidth'($urandom()), AxiProtWidth'($urandom()), NoGapCycles,
                           MidResetResponseStallCycles);
    fork
      begin
        fork
          axil_driver.run(NoWrites, SingleRead);
          apb_completer.run_queue(response_queue, response_controls);
          apb_monitor.run();
          axil_monitor.run();
        join
      end
      begin
        @cb;
        while (!cb.rvalid) @cb;
        td.reset_dut();
      end
      timeout(timeout_tick, MidResetTimeoutCycles,
              "Timeout waiting to reset br_amba_axil2apb during read response", timeout_failed);
    join_any
    disable fork;

    check_mid_reset_abort("reset during AXI-Lite read response", 1, 1'b1);
    check_mid_reset_recovery("reset during AXI-Lite read response");
  endtask

  task automatic test_reset_mid_transaction();
    axil2apb_scenario_t scenario;
    apb_response_t response_queue[$];

    reset_after_incomplete_write();
    reset_during_apb_setup();
    reset_during_apb_access();
    reset_during_write_response();
    reset_during_read_response();

    init_scenario(scenario, NoWrites, directed_transaction_count());
    scenario.apb_wait_cycles = MidResetRecoveryWaitCycles;
    init_idle();
    queue_reads(scenario, response_queue);
    run_queued_scenario("mid-transaction reset recovery traffic", scenario, response_queue);
  endtask

  initial begin
    init_idle();
    td.reset_dut();
    test_reset_idle();
    test_write_no_delay();
    test_read_no_delay();
    test_zero_strobe_write();
    test_apb_pready_write_backpressure();
    test_apb_pready_read_backpressure();
    test_write_data_skew();
    test_write_address_skew();
    test_read_write_arbitration();
    test_axi_write_response_backpressure();
    test_axi_read_response_backpressure();
    test_mixed_response_backpressure();
    test_error_response_propagation();
    test_mixed_directed_sequence();
    test_stress();
    test_reset_mid_transaction();
    td.finish();
  end
endmodule : br_amba_axil2apb_tb
