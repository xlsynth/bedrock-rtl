// SPDX-License-Identifier: Apache-2.0

// Directed simulation testbench for br_amba_atb_funnel.
//
// Scope:
// - Idle after reset with no source traffic.
// - Single-source and multi-source packet preservation.
// - Destination backpressure and source payload stability while stalled.
// - Continuous stress traffic with all sources enabled.
// - Reset asserted during active traffic.
// - Bazel-swept source count, data width, user width, and ready registration.

module br_amba_atb_funnel_tb;
  parameter int NumSources = 3;
  parameter int DataWidth = 32;
  parameter int UserWidth = 2;
  parameter bit RegisterAtReady = 0;

  localparam int ByteCountWidth = $clog2(DataWidth / 8);
  localparam int ResetCycles = 5;
  localparam int TimeoutCycles = 3000;
  localparam int StressBeatsPerSource = 64;

  // Destination ready patterns used to create no-stall and stalled sink behavior.
  typedef enum int {
    ReadyAlways,
    ReadyAlternating,
    ReadyPeriodicStall
  } ready_pattern_t;

  // One ATB beat as sampled by the source and destination monitors.
  typedef struct packed {
    logic [br_amba::AtbIdWidth-1:0] atid;
    logic [DataWidth-1:0] atdata;
    logic [ByteCountWidth-1:0] atbytes;
    logic [UserWidth-1:0] atuser;
  } atb_packet_t;

  // Per-test scenario controls shared by the source driver and sink readiness logic.
  typedef struct packed {
    logic [NumSources-1:0] source_mask;
    int unsigned beats_per_source;
    int unsigned valid_gap_cycles;
    int unsigned min_runtime_cycles;
    ready_pattern_t ready_pattern;
    bit alternate_sources;
    bit check_full_rate;
  } scenario_config_t;

  // Clock and reset driven by br_test_driver.
  logic clk;
  logic rst;
  logic td_rst;
  logic pulse_rst;

  // Source ATB interfaces driven by the testbench into the DUT.
  logic [NumSources-1:0] src_atvalid;
  logic [NumSources-1:0] src_atready;
  logic [NumSources-1:0][br_amba::AtbIdWidth-1:0] src_atid;
  logic [NumSources-1:0][DataWidth-1:0] src_atdata;
  logic [NumSources-1:0][ByteCountWidth-1:0] src_atbytes;
  logic [NumSources-1:0][UserWidth-1:0] src_atuser;

  // Destination ATB interface observed and backpressured by the testbench.
  logic dst_atvalid;
  logic dst_atready;
  logic [br_amba::AtbIdWidth-1:0] dst_atid;
  logic [DataWidth-1:0] dst_atdata;
  logic [ByteCountWidth-1:0] dst_atbytes;
  logic [UserWidth-1:0] dst_atuser;

  // Scenario-level timer and transfer counters.
  logic scenario_timeout_seen;
  int unsigned scenario_timer;
  int unsigned accepted_count;
  int unsigned observed_count;
  logic destination_transfer_seen;

  // Per-source stimulus state for issued beats, gaps, and accepted-beat retirement.
  int unsigned source_sent_count[NumSources];
  int unsigned source_gap_count[NumSources];
  logic [NumSources-1:0] source_accepted_last_cycle;

  // Previous-cycle source state used by background valid/payload stability monitors.
  logic [NumSources-1:0] prev_src_atvalid;
  logic [NumSources-1:0] prev_src_atready;
  logic [NumSources-1:0][br_amba::AtbIdWidth-1:0] prev_src_atid;
  logic [NumSources-1:0][DataWidth-1:0] prev_src_atdata;
  logic [NumSources-1:0][ByteCountWidth-1:0] prev_src_atbytes;
  logic [NumSources-1:0][UserWidth-1:0] prev_src_atuser;

  // Previous-cycle destination state used by background valid/payload stability monitors.
  logic prev_dst_atvalid;
  logic prev_dst_atready;
  logic [br_amba::AtbIdWidth-1:0] prev_dst_atid;
  logic [DataWidth-1:0] prev_dst_atdata;
  logic [ByteCountWidth-1:0] prev_dst_atbytes;
  logic [UserWidth-1:0] prev_dst_atuser;

  // Expected packet order collected from accepted source transfers.
  atb_packet_t expected_packets[$];

  // Received packet order collected from destination transfers.
  atb_packet_t received_packets[$];

  br_amba_atb_funnel #(
      .NumSources(NumSources),
      .DataWidth(DataWidth),
      .UserWidth(UserWidth),
      .RegisterAtReady(RegisterAtReady)
  ) dut (
      .clk(clk),
      .rst(rst),
      .src_atvalid(src_atvalid),
      .src_atready(src_atready),
      .src_atid(src_atid),
      .src_atdata(src_atdata),
      .src_atbytes(src_atbytes),
      .src_atuser(src_atuser),
      .dst_atvalid(dst_atvalid),
      .dst_atready(dst_atready),
      .dst_atid(dst_atid),
      .dst_atdata(dst_atdata),
      .dst_atbytes(dst_atbytes),
      .dst_atuser(dst_atuser)
  );

  br_test_driver #(
      .ResetCycles(ResetCycles)
  ) td (
      .clk(clk),
      .rst(td_rst)
  );

  assign rst = td_rst || pulse_rst;

  function automatic logic [NumSources-1:0] random_source_mask(input int unsigned enabled_sources);
    logic [NumSources-1:0] mask = '0;
    int unsigned target_sources = enabled_sources > NumSources ? NumSources : enabled_sources;
    int unsigned available_sources[$];

    for (int source = 0; source < NumSources; source++) begin
      available_sources.push_back(source);
    end

    for (int count = 0; count < target_sources; count++) begin
      int unsigned selected_position = $urandom_range(available_sources.size() - 1, 0);

      mask[available_sources[selected_position]] = 1'b1;
      available_sources.delete(selected_position);
    end
    return mask;
  endfunction

  function automatic int selected_alternating_source(input logic [NumSources-1:0] source_mask,
                                                     input int unsigned beats_per_source);
    for (int offset = 0; offset < NumSources; offset++) begin
      int source = (scenario_timer + offset) % NumSources;

      if (source_mask[source] && source_sent_count[source] < beats_per_source) begin
        return source;
      end
    end

    return NumSources;
  endfunction

  function automatic bit ready_for_timer(input ready_pattern_t pattern);
    case (pattern)
      ReadyAlways: return 1'b1;
      ReadyAlternating: return scenario_timer[0];
      ReadyPeriodicStall: return (scenario_timer % 7) >= 3;
      default: return 1'b0;
    endcase
  endfunction

  function automatic atb_packet_t make_packet();
    atb_packet_t packet;

    packet.atid = br_amba::AtbIdWidth'($urandom);
    packet.atdata = DataWidth'({$urandom, $urandom});
    packet.atbytes = ByteCountWidth'($urandom);
    packet.atuser = UserWidth'($urandom);
    return packet;
  endfunction

  // Clears one source interface after reset, completion, or an accepted transfer.
  task automatic clear_source(input int source);
    src_atvalid[source] = 1'b0;
    src_atid[source] = '0;
    src_atdata[source] = '0;
    src_atbytes[source] = '0;
    src_atuser[source] = '0;
  endtask

  // Generates and drives a new randomized packet for one source.
  task automatic drive_source_packet(input int source);
    atb_packet_t packet = make_packet();

    src_atvalid[source] = 1'b1;
    src_atid[source] = packet.atid;
    src_atdata[source] = packet.atdata;
    src_atbytes[source] = packet.atbytes;
    src_atuser[source] = packet.atuser;
  endtask

  // Returns the bench-controlled interfaces, counters, and history state to idle.
  task automatic init_signals();
    src_atvalid = '0;
    src_atid = '0;
    src_atdata = '0;
    src_atbytes = '0;
    src_atuser = '0;
    pulse_rst = 1'b0;
    dst_atready = 1'b1;
    scenario_timer = 0;
    destination_transfer_seen = 1'b0;
    source_accepted_last_cycle = '0;
    prev_src_atvalid = '0;
    prev_src_atready = '0;
    prev_src_atid = '0;
    prev_src_atdata = '0;
    prev_src_atbytes = '0;
    prev_src_atuser = '0;
    prev_dst_atvalid = 1'b0;
    prev_dst_atready = 1'b0;
    prev_dst_atid = '0;
    prev_dst_atdata = '0;
    prev_dst_atbytes = '0;
    prev_dst_atuser = '0;
    expected_packets.delete();
    received_packets.delete();
  endtask

  // Initializes per-source counters and clears any pending source gaps.
  task automatic init_source_state(input logic [NumSources-1:0] source_mask);
    for (int source = 0; source < NumSources; source++) begin
      source_sent_count[source] = 0;
      source_gap_count[source]  = 0;
      clear_source(source);
    end

    source_accepted_last_cycle = '0;
  endtask

  // Checks source and destination stability, then samples state for the next cycle.
  task automatic monitor_stability();
    forever begin
      @(posedge clk);

      for (int source = 0; source < NumSources; source++) begin
        if (!rst && prev_src_atvalid[source] && !prev_src_atready[source]) begin
          td.check(src_atvalid[source], $sformatf(
                   "source %0d dropped valid while backpressured", source));
          td.check(
              src_atid[source] === prev_src_atid[source] &&
                   src_atdata[source] === prev_src_atdata[source] &&
                   src_atbytes[source] === prev_src_atbytes[source] &&
                   src_atuser[source] === prev_src_atuser[source],
              $sformatf("source %0d changed payload while backpressured", source));
        end
      end

      if (!rst && prev_dst_atvalid && !prev_dst_atready) begin
        td.check(dst_atvalid, "destination dropped valid while backpressured");
        td.check(
            dst_atid === prev_dst_atid && dst_atdata === prev_dst_atdata &&
                 dst_atbytes === prev_dst_atbytes && dst_atuser === prev_dst_atuser,
            "destination changed payload while backpressured");
      end

      prev_src_atvalid = src_atvalid;
      prev_src_atready = src_atready;
      prev_src_atid = src_atid;
      prev_src_atdata = src_atdata;
      prev_src_atbytes = src_atbytes;
      prev_src_atuser = src_atuser;
      prev_dst_atvalid = dst_atvalid;
      prev_dst_atready = dst_atready;
      prev_dst_atid = dst_atid;
      prev_dst_atdata = dst_atdata;
      prev_dst_atbytes = dst_atbytes;
      prev_dst_atuser = dst_atuser;
    end
  endtask

  // Monitors that the destination is idle once no source is valid and all queued beats drained.
  task automatic monitor_idle_source_to_destination(input string scenario_name);
    forever begin
      @(posedge clk);

      if (!(|src_atvalid) && !(dst_atvalid && dst_atready) &&
          expected_packets.size() == received_packets.size()) begin
        td.check(!dst_atvalid, $sformatf(
                 "%s destination valid while sources are idle", scenario_name));
      end
    end
  endtask

  // Records accepted source packets into the expected queue in the background.
  task automatic monitor_source_transfers(input int unsigned expected_transfers,
                                          input string scenario_name);
    forever begin
      @(posedge clk);
      begin
        int unsigned accepts_this_cycle = 0;

        for (int source = 0; source < NumSources; source++) begin
          if (!rst && src_atvalid[source] && src_atready[source]) begin
            atb_packet_t packet;

            packet.atid = src_atid[source];
            packet.atdata = src_atdata[source];
            packet.atbytes = src_atbytes[source];
            packet.atuser = src_atuser[source];
            expected_packets.push_back(packet);
            source_sent_count[source]++;
            source_accepted_last_cycle[source] = 1'b1;
            accepted_count++;
            accepts_this_cycle++;
          end else begin
            source_accepted_last_cycle[source] = 1'b0;
          end
        end

        td.check(accepts_this_cycle <= 1, "more than one source transfer accepted in a cycle");
        td.check(accepted_count <= expected_transfers, $sformatf(
                 "%s accepted more source transfers than expected", scenario_name));
      end
    end
  endtask

  // Records destination transfers into the received queue in the background.
  task automatic monitor_destination_transfers(input int unsigned expected_transfers,
                                               input string scenario_name);
    forever begin
      @(posedge clk);
      begin
        bit transfer_seen = !rst && dst_atvalid && dst_atready;

        destination_transfer_seen = transfer_seen;

        if (transfer_seen) begin
          atb_packet_t packet;

          packet.atid = dst_atid;
          packet.atdata = dst_atdata;
          packet.atbytes = dst_atbytes;
          packet.atuser = dst_atuser;
          received_packets.push_back(packet);
          observed_count++;
        end

        td.check(observed_count <= expected_transfers, $sformatf(
                 "%s observed more destination transfers than expected", scenario_name));
      end
    end
  endtask

  // Checks source and destination transfer counts, then compares packet payloads.
  task automatic check_recorded_packets(input string scenario_name,
                                        input int unsigned expected_transfers);
    td.check_integer(accepted_count, expected_transfers, $sformatf(
                     "%s source transfer count mismatch", scenario_name));
    td.check_integer(observed_count, expected_transfers, $sformatf(
                     "%s destination transfer count mismatch", scenario_name));
    td.check_integer(expected_packets.size(), expected_transfers, $sformatf(
                     "%s expected packet count mismatch", scenario_name));
    td.check_integer(received_packets.size(), expected_transfers, $sformatf(
                     "%s received packet count mismatch", scenario_name));

    for (int packet = 0; packet < expected_transfers; packet++) begin
      if (packet < expected_packets.size() && packet < received_packets.size()) begin
        td.check(received_packets[packet].atid === expected_packets[packet].atid, $sformatf(
                 "%s packet %0d ATID mismatch", scenario_name, packet));
        td.check(received_packets[packet].atdata === expected_packets[packet].atdata, $sformatf(
                 "%s packet %0d ATDATA mismatch", scenario_name, packet));
        td.check(received_packets[packet].atbytes === expected_packets[packet].atbytes, $sformatf(
                 "%s packet %0d ATBYTES mismatch", scenario_name, packet));
        td.check(received_packets[packet].atuser === expected_packets[packet].atuser, $sformatf(
                 "%s packet %0d ATUSER mismatch", scenario_name, packet));
      end
    end
  endtask

  // Drives enabled sources, optionally rotating which source may launch next.
  task automatic drive_sources(input logic [NumSources-1:0] source_mask,
                               input int unsigned beats_per_source,
                               input int unsigned valid_gap_cycles, input bit alternate_sources);
    int selected_source = alternate_sources ? selected_alternating_source(
        source_mask, beats_per_source
    ) : NumSources;
    bit pending_alternating_valid = 1'b0;

    for (int source = 0; source < NumSources; source++) begin
      pending_alternating_valid |= src_atvalid[source] && !source_accepted_last_cycle[source];
    end

    for (int source = 0; source < NumSources; source++) begin
      if (source_accepted_last_cycle[source]) begin
        // Retire the accepted beat; if no gap is selected, immediately offer the next packet.
        if (source_mask[source] && source_sent_count[source] < beats_per_source) begin
          int unsigned gap_cycles = $urandom_range(valid_gap_cycles, 0);

          if (!alternate_sources && gap_cycles == 0) begin
            drive_source_packet(source);
          end else begin
            clear_source(source);
            source_gap_count[source] = gap_cycles == 0 ? 0 : gap_cycles - 1;
          end
        end else begin
          clear_source(source);
        end
      end else if (!source_mask[source] || source_sent_count[source] >= beats_per_source) begin
        // Keep inactive and completed sources idle.
        clear_source(source);
      end else if (src_atvalid[source]) begin
        // Hold valid and payload stable until the DUT accepts the transfer.
        src_atvalid[source] = 1'b1;
      end else if (alternate_sources &&
                   (pending_alternating_valid || source != selected_source)) begin
        // In alternating mode, allow only the selected source to issue a new transfer.
        clear_source(source);
      end else if (source_gap_count[source] != 0) begin
        // Wait out the randomized inter-transfer gap before issuing the next packet.
        source_gap_count[source]--;
        clear_source(source);
      end else begin
        // Source is enabled, not stalled by a gap, and ready to offer a new packet.
        drive_source_packet(source);
      end
    end
  endtask

  // Deasserts all source valids and clears per-source accept bookkeeping.
  task automatic clear_all_sources();
    for (int source = 0; source < NumSources; source++) begin
      clear_source(source);
    end

    source_accepted_last_cycle = '0;
  endtask

  // Tracks scenario runtime independently from the source stimulus driver.
  task automatic timeout(input string scenario_name);
    while (scenario_timer < TimeoutCycles) begin
      @(posedge clk);
      scenario_timer++;
    end

    scenario_timeout_seen = 1'b1;
    td.check(1'b0, $sformatf("%s timed out", scenario_name));

    forever begin
      @(posedge clk);
    end
  endtask

  // Runs one reset-aware scenario and checks ordering, counts, stability, and timeout.
  task automatic run_scenario(input string scenario_name, input scenario_config_t scenario);
    int unsigned expected_transfers = $countones(scenario.source_mask) * scenario.beats_per_source;
    bit done = 1'b0;

    scenario_timeout_seen = 1'b0;
    scenario_timer = 0;
    accepted_count = 0;
    observed_count = 0;
    destination_transfer_seen = 1'b0;
    expected_packets.delete();
    received_packets.delete();
    init_source_state(scenario.source_mask);

    $display("Running %s: mask=0x%0h beats=%0d gap_bound=%0d min_cycles=%0d", scenario_name,
             scenario.source_mask, scenario.beats_per_source, scenario.valid_gap_cycles,
             scenario.min_runtime_cycles);
    $display("  ready=%0d alt=%0b full_rate=%0b", scenario.ready_pattern,
             scenario.alternate_sources, scenario.check_full_rate);

    fork
      monitor_stability();
      monitor_idle_source_to_destination(scenario_name);
      monitor_source_transfers(expected_transfers, scenario_name);
      monitor_destination_transfers(expected_transfers, scenario_name);
      timeout(scenario_name);
    join_none

    while (!done && !scenario_timeout_seen) begin
      @(negedge clk);

      done = accepted_count == expected_transfers &&
             observed_count == expected_transfers &&
             expected_packets.size() == expected_transfers &&
             received_packets.size() == expected_transfers &&
             scenario_timer >= scenario.min_runtime_cycles;

      if (scenario.check_full_rate && !rst && observed_count != 0 &&
          observed_count < expected_transfers) begin
        td.check(destination_transfer_seen, $sformatf(
                 "%s inserted a destination transfer bubble", scenario_name));
      end

      if (!done && !scenario_timeout_seen) begin
        dst_atready = ready_for_timer(scenario.ready_pattern);
        if (rst) begin
          clear_all_sources();
        end else begin
          drive_sources(scenario.source_mask, scenario.beats_per_source, scenario.valid_gap_cycles,
                        scenario.alternate_sources);
        end
      end
    end

    disable fork;

    check_recorded_packets(scenario_name, expected_transfers);

    @(negedge clk);
    clear_all_sources();
    dst_atready = 1'b1;
  endtask

  // Intent: verify the DUT stays idle after reset with no source traffic.
  task automatic test_smoke();
    td.reset_dut();
    init_signals();
    run_scenario("smoke",
                 '{
                     source_mask: '0,
                     beats_per_source: 0,
                     valid_gap_cycles: 0,
                     min_runtime_cycles: $urandom_range(20, 10),
                     ready_pattern: ReadyAlways,
                     alternate_sources: 1'b0,
                     check_full_rate: 1'b0
                 });
  endtask

  // Intent: verify one active source can stream at full rate without output bubbles.
  task automatic test_single_source_full_rate();
    td.reset_dut();
    init_signals();
    run_scenario("single_source_full_rate",
                 '{
                     source_mask: random_source_mask(1),
                     beats_per_source: $urandom_range(24, 16),
                     valid_gap_cycles: 0,
                     min_runtime_cycles: 0,
                     ready_pattern: ReadyAlways,
                     alternate_sources: 1'b0,
                     check_full_rate: 1'b1
                 });
  endtask

  // Intent: verify randomized multi-source traffic while rotating active sources.
  task automatic test_multi_source_basic();
    int unsigned multi_source_count = $urandom_range(NumSources, 2);

    td.reset_dut();
    init_signals();
    run_scenario("multi_source_basic",
                 '{
                     source_mask: random_source_mask(multi_source_count),
                     beats_per_source: $urandom_range(10, 4),
                     valid_gap_cycles: 0,
                     min_runtime_cycles: 0,
                     ready_pattern: ReadyAlways,
                     alternate_sources: 1'b1,
                     check_full_rate: 1'b0
                 });
  endtask

  // Intent: verify payload stability and ordering under destination stalls.
  task automatic test_destination_backpressure();
    td.reset_dut();
    init_signals();
    run_scenario("destination_backpressure",
                 '{
                     source_mask: random_source_mask(NumSources),
                     beats_per_source: $urandom_range(12, 5),
                     valid_gap_cycles: $urandom_range(6, 2),
                     min_runtime_cycles: 0,
                     ready_pattern: ReadyPeriodicStall,
                     alternate_sources: 1'b0,
                     check_full_rate: 1'b0
                 });
  endtask

  // Intent: verify continuous all-source traffic with no source gaps or backpressure.
  task automatic test_stress();
    td.reset_dut();
    init_signals();
    run_scenario("stress",
                 '{
                     source_mask: random_source_mask(NumSources),
                     beats_per_source: StressBeatsPerSource,
                     valid_gap_cycles: 0,
                     min_runtime_cycles: 0,
                     ready_pattern: ReadyAlways,
                     alternate_sources: 1'b0,
                     check_full_rate: 1'b1
                 });
  endtask

  // Waits for active traffic, pulses reset, and restarts scenario accounting.
  task automatic pulse_reset_after_transfers(input int unsigned reset_after_transfers,
                                             input logic [NumSources-1:0] source_mask);
    while ((observed_count < reset_after_transfers || !(|src_atvalid) && !dst_atvalid) &&
           !scenario_timeout_seen) begin
      @(posedge clk);
    end

    @(negedge clk);
    pulse_rst = 1'b1;
    clear_all_sources();
    accepted_count = 0;
    observed_count = 0;
    expected_packets.delete();
    received_packets.delete();
    init_source_state(source_mask);
    td.wait_cycles(ResetCycles);
    td.check(!dst_atvalid, "destination valid during reset while active");
    pulse_rst = 1'b0;
  endtask

  // Intent: verify reset can interrupt an active scenario without blocking post-reset completion.
  task automatic test_reset_while_active();
    logic [NumSources-1:0] source_mask = random_source_mask(2);
    scenario_config_t scenario = '{
        source_mask: source_mask,
        beats_per_source: 8,
        valid_gap_cycles: 0,
        min_runtime_cycles: 0,
        ready_pattern: ReadyAlways,
        alternate_sources: 1'b0,
        check_full_rate: 1'b0
    };
    int unsigned reset_after_transfers = ($countones(source_mask) * scenario.beats_per_source) / 2;

    td.reset_dut();
    init_signals();

    fork
      run_scenario("reset_while_active", scenario);
      pulse_reset_after_transfers(reset_after_transfers, source_mask);
    join
  endtask

  initial begin
    test_smoke();
    test_single_source_full_rate();
    test_multi_source_basic();
    test_destination_backpressure();
    test_stress();
    test_reset_while_active();

    td.finish(10);
  end

endmodule : br_amba_atb_funnel_tb
