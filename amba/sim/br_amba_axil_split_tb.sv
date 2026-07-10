// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;
import br_amba_axil_monitor_sim_pkg::*;
import br_amba_axil_split_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_asserts.svh"
`include "br_amba_sim_macros.svh"

// Directed simulation testbench for br_amba_axil_split. The scenarios cover route smoke tests,
// range boundaries and overlaps, channel skew, backpressure, outstanding depth, randomized traffic,
// and reset recovery. Split-specific prediction and data checks live in the scoreboard.
module br_amba_axil_split_tb;
  // Testbench clock/reset and global scenario timeout.
  localparam int ResetCycles = 5;
  localparam int ClockPeriodNs = 10;
  localparam int TimeoutCycles = 100000;

  // Common transaction-count aliases for directed scenarios.
  localparam int NoWrites = 0;
  localparam int NoReads = 0;
  localparam int SingleWrite = 1;
  localparam int SingleRead = 1;

  // Default no-delay channel timing used by init_scenario.
  localparam int NoGapCycles = 0;
  localparam int NoStallCycles = 0;

  // Directed timing knobs shared by write-skew, outstanding, and reset scenarios.
  localparam int WriteSkewGapCycles = 4;
  localparam int OutstandingResponseStallCycles = 8;
  localparam int MidResetResponseStallCycles = 8;
  localparam int MidResetTimeoutCycles = 64;

  // Bounded random traffic size for directed backpressure and mixed-traffic scenarios.
  localparam int MinDirectedTransactions = 20;
  localparam int MaxDirectedTransactions = 40;

  // Address-space endpoints used by branch range generation and boundary tests.
  localparam logic [AxilAddrWidth-1:0] MinAxilAddr = '0;
  localparam logic [AxilAddrWidth-1:0] MaxAxilAddr = '1;
  localparam logic [AxilAddrWidth-1:0] MaxBranchRangeAddr = MaxAxilAddr - AxilAddrWidth'(1);

  // DUT parameters swept by the Bazel simulation matrix.
  parameter int MaxOutstandingReads = 1;
  parameter int MaxOutstandingWrites = 1;
  parameter int NumBranchAddrRanges = 1;
  parameter int MinRandomDelayCycles = 0;
  parameter int MaxRandomDelayCycles = 3;
  parameter bit NormalizeBranchAddress = 0;

  localparam int NumBranchRanges = NumBranchAddrRanges;

  `BR_ASSERT_STATIC(NumBranchRangesPositive, NumBranchRanges > 0)
  `BR_ASSERT_STATIC(MinRandomDelayCyclesNonnegative, MinRandomDelayCycles >= 0)
  `BR_ASSERT_STATIC(RandomDelayRangeValid, MaxRandomDelayCycles >= MinRandomDelayCycles)

  // Widened arithmetic type for address-range generation without wraparound.
  localparam int AddrCalcWidth = AxilAddrWidth + $clog2(NumBranchRanges + 1) + 1;

  logic clk;
  logic rst;
  logic root_driver_failed;
  logic trunk_target_failed;
  logic branch_target_failed;
  logic root_monitor_failed;
  logic trunk_monitor_failed;
  logic branch_monitor_failed;
  logic scoreboard_failed;
  logic timeout_failed;
  logic reset_monitor_enabled = 1'b0;
  event timeout_tick;

  logic [NumBranchRanges-1:0][AxilAddrWidth-1:0] branch_start_addr;
  logic [NumBranchRanges-1:0][AxilAddrWidth-1:0] branch_end_addr;

  // AXI4-Lite root target interface.
  logic [AxilAddrWidth-1:0] root_awaddr;
  logic [AxiProtWidth-1:0] root_awprot;
  logic [AxilUserWidth-1:0] root_awuser;
  logic root_awvalid;
  logic root_awready;
  logic [AxilDataWidth-1:0] root_wdata;
  logic [AxilStrobeWidth-1:0] root_wstrb;
  logic [AxilUserWidth-1:0] root_wuser;
  logic root_wvalid;
  logic root_wready;
  logic [AxiRespWidth-1:0] root_bresp;
  logic root_bvalid;
  logic root_bready;
  logic [AxilAddrWidth-1:0] root_araddr;
  logic [AxiProtWidth-1:0] root_arprot;
  logic [AxilUserWidth-1:0] root_aruser;
  logic root_arvalid;
  logic root_arready;
  logic [AxilDataWidth-1:0] root_rdata;
  logic [AxiRespWidth-1:0] root_rresp;
  logic [AxilUserWidth-1:0] root_ruser;
  logic root_rvalid;
  logic root_rready;

  // AXI4-Lite trunk initiator interface.
  logic [AxilAddrWidth-1:0] trunk_awaddr;
  logic [AxiProtWidth-1:0] trunk_awprot;
  logic [AxilUserWidth-1:0] trunk_awuser;
  logic trunk_awvalid;
  logic trunk_awready;
  logic [AxilDataWidth-1:0] trunk_wdata;
  logic [AxilStrobeWidth-1:0] trunk_wstrb;
  logic [AxilUserWidth-1:0] trunk_wuser;
  logic trunk_wvalid;
  logic trunk_wready;
  logic [AxiRespWidth-1:0] trunk_bresp;
  logic [AxilUserWidth-1:0] trunk_buser;
  logic trunk_bvalid;
  logic trunk_bready;
  logic [AxilAddrWidth-1:0] trunk_araddr;
  logic [AxiProtWidth-1:0] trunk_arprot;
  logic [AxilUserWidth-1:0] trunk_aruser;
  logic trunk_arvalid;
  logic trunk_arready;
  logic [AxilDataWidth-1:0] trunk_rdata;
  logic [AxiRespWidth-1:0] trunk_rresp;
  logic [AxilUserWidth-1:0] trunk_ruser;
  logic trunk_rvalid;
  logic trunk_rready;

  // AXI4-Lite branch initiator interface.
  logic [AxilAddrWidth-1:0] branch_awaddr;
  logic [AxiProtWidth-1:0] branch_awprot;
  logic [AxilUserWidth-1:0] branch_awuser;
  logic branch_awvalid;
  logic branch_awready;
  logic [AxilDataWidth-1:0] branch_wdata;
  logic [AxilStrobeWidth-1:0] branch_wstrb;
  logic [AxilUserWidth-1:0] branch_wuser;
  logic branch_wvalid;
  logic branch_wready;
  logic [AxiRespWidth-1:0] branch_bresp;
  logic [AxilUserWidth-1:0] branch_buser;
  logic branch_bvalid;
  logic branch_bready;
  logic [AxilAddrWidth-1:0] branch_araddr;
  logic [AxiProtWidth-1:0] branch_arprot;
  logic [AxilUserWidth-1:0] branch_aruser;
  logic branch_arvalid;
  logic branch_arready;
  logic [AxilDataWidth-1:0] branch_rdata;
  logic [AxiRespWidth-1:0] branch_rresp;
  logic [AxilUserWidth-1:0] branch_ruser;
  logic branch_rvalid;
  logic branch_rready;

  always @(posedge clk) begin
    ->timeout_tick;
  end

  br_test_driver #(
      .ResetCycles  (ResetCycles),
      .ClockPeriodNs(ClockPeriodNs)
  ) td (
      .clk(clk),
      .rst(rst)
  );

  br_amba_axil_split #(
      .AddrWidth(AxilAddrWidth),
      .DataWidth(AxilDataWidth),
      .AWUserWidth(AxilUserWidth),
      .WUserWidth(AxilUserWidth),
      .ARUserWidth(AxilUserWidth),
      .RUserWidth(AxilUserWidth),
      .MaxOutstandingReads(MaxOutstandingReads),
      .MaxOutstandingWrites(MaxOutstandingWrites),
      .NumBranchAddrRanges(NumBranchRanges),
      .NormalizeBranchAddress(NormalizeBranchAddress)
  ) dut (
      .clk(clk),
      .rst(rst),
      .branch_start_addr(branch_start_addr),
      .branch_end_addr(branch_end_addr),
      .root_awaddr(root_awaddr),
      .root_awprot(root_awprot),
      .root_awuser(root_awuser),
      .root_awvalid(root_awvalid),
      .root_awready(root_awready),
      .root_wdata(root_wdata),
      .root_wstrb(root_wstrb),
      .root_wuser(root_wuser),
      .root_wvalid(root_wvalid),
      .root_wready(root_wready),
      .root_bresp(root_bresp),
      .root_bvalid(root_bvalid),
      .root_bready(root_bready),
      .root_araddr(root_araddr),
      .root_arprot(root_arprot),
      .root_aruser(root_aruser),
      .root_arvalid(root_arvalid),
      .root_arready(root_arready),
      .root_rdata(root_rdata),
      .root_rresp(root_rresp),
      .root_ruser(root_ruser),
      .root_rvalid(root_rvalid),
      .root_rready(root_rready),
      .trunk_awaddr(trunk_awaddr),
      .trunk_awprot(trunk_awprot),
      .trunk_awuser(trunk_awuser),
      .trunk_awvalid(trunk_awvalid),
      .trunk_awready(trunk_awready),
      .trunk_wdata(trunk_wdata),
      .trunk_wstrb(trunk_wstrb),
      .trunk_wuser(trunk_wuser),
      .trunk_wvalid(trunk_wvalid),
      .trunk_wready(trunk_wready),
      .trunk_bresp(trunk_bresp),
      .trunk_bvalid(trunk_bvalid),
      .trunk_bready(trunk_bready),
      .trunk_araddr(trunk_araddr),
      .trunk_arprot(trunk_arprot),
      .trunk_aruser(trunk_aruser),
      .trunk_arvalid(trunk_arvalid),
      .trunk_arready(trunk_arready),
      .trunk_rdata(trunk_rdata),
      .trunk_rresp(trunk_rresp),
      .trunk_ruser(trunk_ruser),
      .trunk_rvalid(trunk_rvalid),
      .trunk_rready(trunk_rready),
      .branch_awaddr(branch_awaddr),
      .branch_awprot(branch_awprot),
      .branch_awuser(branch_awuser),
      .branch_awvalid(branch_awvalid),
      .branch_awready(branch_awready),
      .branch_wdata(branch_wdata),
      .branch_wstrb(branch_wstrb),
      .branch_wuser(branch_wuser),
      .branch_wvalid(branch_wvalid),
      .branch_wready(branch_wready),
      .branch_bresp(branch_bresp),
      .branch_bvalid(branch_bvalid),
      .branch_bready(branch_bready),
      .branch_araddr(branch_araddr),
      .branch_arprot(branch_arprot),
      .branch_aruser(branch_aruser),
      .branch_arvalid(branch_arvalid),
      .branch_arready(branch_arready),
      .branch_rdata(branch_rdata),
      .branch_rresp(branch_rresp),
      .branch_ruser(branch_ruser),
      .branch_rvalid(branch_rvalid),
      .branch_rready(branch_rready)
  );

  br_amba_axil_requester_driver #(
      .AddrWidth(AxilAddrWidth),
      .DataWidth(AxilDataWidth),
      .AWUserWidth(AxilUserWidth),
      .WUserWidth(AxilUserWidth),
      .ARUserWidth(AxilUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) root_driver (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(root_awaddr),
      .axil_awprot(root_awprot),
      .axil_awuser(root_awuser),
      .axil_awvalid(root_awvalid),
      .axil_awready(root_awready),
      .axil_wdata(root_wdata),
      .axil_wstrb(root_wstrb),
      .axil_wuser(root_wuser),
      .axil_wvalid(root_wvalid),
      .axil_wready(root_wready),
      .axil_bvalid(root_bvalid),
      .axil_bready(root_bready),
      .axil_araddr(root_araddr),
      .axil_arprot(root_arprot),
      .axil_aruser(root_aruser),
      .axil_arvalid(root_arvalid),
      .axil_arready(root_arready),
      .axil_rvalid(root_rvalid),
      .axil_rready(root_rready),
      .failed(root_driver_failed)
  );

  br_amba_axil_target_driver #(
      .DataWidth(AxilDataWidth),
      .BUserWidth(AxilUserWidth),
      .RUserWidth(AxilUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) trunk_target (
      .clk(clk),
      .rst(rst),
      .axil_awvalid(trunk_awvalid),
      .axil_awready(trunk_awready),
      .axil_wvalid(trunk_wvalid),
      .axil_wready(trunk_wready),
      .axil_bresp(trunk_bresp),
      .axil_buser(trunk_buser),
      .axil_bvalid(trunk_bvalid),
      .axil_bready(trunk_bready),
      .axil_arvalid(trunk_arvalid),
      .axil_arready(trunk_arready),
      .axil_rdata(trunk_rdata),
      .axil_rresp(trunk_rresp),
      .axil_ruser(trunk_ruser),
      .axil_rvalid(trunk_rvalid),
      .axil_rready(trunk_rready),
      .failed(trunk_target_failed)
  );

  br_amba_axil_target_driver #(
      .DataWidth(AxilDataWidth),
      .BUserWidth(AxilUserWidth),
      .RUserWidth(AxilUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) branch_target (
      .clk(clk),
      .rst(rst),
      .axil_awvalid(branch_awvalid),
      .axil_awready(branch_awready),
      .axil_wvalid(branch_wvalid),
      .axil_wready(branch_wready),
      .axil_bresp(branch_bresp),
      .axil_buser(branch_buser),
      .axil_bvalid(branch_bvalid),
      .axil_bready(branch_bready),
      .axil_arvalid(branch_arvalid),
      .axil_arready(branch_arready),
      .axil_rdata(branch_rdata),
      .axil_rresp(branch_rresp),
      .axil_ruser(branch_ruser),
      .axil_rvalid(branch_rvalid),
      .axil_rready(branch_rready),
      .failed(branch_target_failed)
  );

  br_amba_axil_monitor #(
      .AddrWidth  (AxilAddrWidth),
      .DataWidth  (AxilDataWidth),
      .AWUserWidth(AxilUserWidth),
      .WUserWidth (AxilUserWidth),
      .BUserWidth (AxilUserWidth),
      .ARUserWidth(AxilUserWidth),
      .RUserWidth (AxilUserWidth)
  ) root_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(root_awaddr),
      .axil_awprot(root_awprot),
      .axil_awuser(root_awuser),
      .axil_awvalid(root_awvalid),
      .axil_awready(root_awready),
      .axil_wdata(root_wdata),
      .axil_wstrb(root_wstrb),
      .axil_wuser(root_wuser),
      .axil_wvalid(root_wvalid),
      .axil_wready(root_wready),
      .axil_bresp(root_bresp),
      .axil_buser('0),
      .axil_bvalid(root_bvalid),
      .axil_bready(root_bready),
      .axil_araddr(root_araddr),
      .axil_arprot(root_arprot),
      .axil_aruser(root_aruser),
      .axil_arvalid(root_arvalid),
      .axil_arready(root_arready),
      .axil_rdata(root_rdata),
      .axil_rresp(root_rresp),
      .axil_ruser(root_ruser),
      .axil_rvalid(root_rvalid),
      .axil_rready(root_rready),
      .failed(root_monitor_failed)
  );

  br_amba_axil_monitor #(
      .AddrWidth  (AxilAddrWidth),
      .DataWidth  (AxilDataWidth),
      .AWUserWidth(AxilUserWidth),
      .WUserWidth (AxilUserWidth),
      .BUserWidth (AxilUserWidth),
      .ARUserWidth(AxilUserWidth),
      .RUserWidth (AxilUserWidth)
  ) trunk_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(trunk_awaddr),
      .axil_awprot(trunk_awprot),
      .axil_awuser(trunk_awuser),
      .axil_awvalid(trunk_awvalid),
      .axil_awready(trunk_awready),
      .axil_wdata(trunk_wdata),
      .axil_wstrb(trunk_wstrb),
      .axil_wuser(trunk_wuser),
      .axil_wvalid(trunk_wvalid),
      .axil_wready(trunk_wready),
      .axil_bresp(trunk_bresp),
      .axil_buser(trunk_buser),
      .axil_bvalid(trunk_bvalid),
      .axil_bready(trunk_bready),
      .axil_araddr(trunk_araddr),
      .axil_arprot(trunk_arprot),
      .axil_aruser(trunk_aruser),
      .axil_arvalid(trunk_arvalid),
      .axil_arready(trunk_arready),
      .axil_rdata(trunk_rdata),
      .axil_rresp(trunk_rresp),
      .axil_ruser(trunk_ruser),
      .axil_rvalid(trunk_rvalid),
      .axil_rready(trunk_rready),
      .failed(trunk_monitor_failed)
  );

  br_amba_axil_monitor #(
      .AddrWidth  (AxilAddrWidth),
      .DataWidth  (AxilDataWidth),
      .AWUserWidth(AxilUserWidth),
      .WUserWidth (AxilUserWidth),
      .BUserWidth (AxilUserWidth),
      .ARUserWidth(AxilUserWidth),
      .RUserWidth (AxilUserWidth)
  ) branch_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr(branch_awaddr),
      .axil_awprot(branch_awprot),
      .axil_awuser(branch_awuser),
      .axil_awvalid(branch_awvalid),
      .axil_awready(branch_awready),
      .axil_wdata(branch_wdata),
      .axil_wstrb(branch_wstrb),
      .axil_wuser(branch_wuser),
      .axil_wvalid(branch_wvalid),
      .axil_wready(branch_wready),
      .axil_bresp(branch_bresp),
      .axil_buser(branch_buser),
      .axil_bvalid(branch_bvalid),
      .axil_bready(branch_bready),
      .axil_araddr(branch_araddr),
      .axil_arprot(branch_arprot),
      .axil_aruser(branch_aruser),
      .axil_arvalid(branch_arvalid),
      .axil_arready(branch_arready),
      .axil_rdata(branch_rdata),
      .axil_rresp(branch_rresp),
      .axil_ruser(branch_ruser),
      .axil_rvalid(branch_rvalid),
      .axil_rready(branch_rready),
      .failed(branch_monitor_failed)
  );

  br_amba_axil_split_scoreboard #(
      .NumBranchAddrRanges(NumBranchRanges),
      .NormalizeBranchAddress(NormalizeBranchAddress)
  ) scoreboard (
      .failed(scoreboard_failed)
  );

  int num_trunk_writes;
  int num_trunk_reads;
  int num_branch_writes;
  int num_branch_reads;
  logic [AxilAddrWidth-1:0] trunk_addr_q[$];
  logic [AxilAddrWidth-1:0] branch_addr_q[$];

  function automatic logic [AxilAddrWidth-1:0] random_addr(
      input logic [AxilAddrWidth-1:0] min_value, input logic [AxilAddrWidth-1:0] max_value);
    logic [  AxilAddrWidth:0] span = {1'b0, max_value} - {1'b0, min_value} + 1'b1;
    logic [AxilAddrWidth-1:0] random_addr_bits;

    `BR_SIM_RANDOMIZE((random_addr_bits), "AXI-Lite split address bits");
    random_addr = min_value + AxilAddrWidth'({1'b0, random_addr_bits} % span);
  endfunction

  function automatic logic is_branch_addr(input logic [AxilAddrWidth-1:0] addr);
    is_branch_addr = 1'b0;
    for (int i = 0; i < NumBranchRanges; i++) begin
      is_branch_addr |= addr >= branch_start_addr[i] && addr <= branch_end_addr[i];
    end
  endfunction

  // Route-directed stimulus is derived from the same branch range state driven into the DUT.
  task automatic populate_addr_queues();
    logic [AxilAddrWidth-1:0] trunk_candidate;

    trunk_addr_q.delete();
    branch_addr_q.delete();
    for (int i = 0; i < NumBranchRanges; i++) begin
      branch_addr_q.push_back(branch_start_addr[i]);
      branch_addr_q.push_back(branch_end_addr[i]);
      if (branch_start_addr[i] != MinAxilAddr) begin
        trunk_candidate = branch_start_addr[i] - AxilAddrWidth'(1);
        if (!is_branch_addr(trunk_candidate)) trunk_addr_q.push_back(trunk_candidate);
      end
      if (branch_end_addr[i] != MaxAxilAddr) begin
        trunk_candidate = branch_end_addr[i] + AxilAddrWidth'(1);
        if (!is_branch_addr(trunk_candidate)) trunk_addr_q.push_back(trunk_candidate);
      end
    end
    if (trunk_addr_q.size() == 0) trunk_addr_q.push_back(MaxAxilAddr);
    td.check(trunk_addr_q.size() != 0, "No trunk address available outside branch ranges");
  endtask

  task automatic init_empty_ranges();
    for (int i = 0; i < NumBranchRanges; i++) begin
      branch_start_addr[i] = MinAxilAddr;
      branch_end_addr[i]   = MinAxilAddr;
    end
  endtask

  task automatic init_disjoint_ranges(input logic [AddrCalcWidth-1:0] addr_space_size);
    logic [NumBranchRanges-1:0][AxilAddrWidth-1:0] range_start_addr;

    if (addr_space_size < AddrCalcWidth'(NumBranchRanges)) begin
      td.check(1'b0, "AXI-Lite address space cannot fit requested non-overlapping branch ranges");
      init_empty_ranges();
      return;
    end

    for (int i = 0; i < NumBranchRanges; i++) begin
      logic [AddrCalcWidth-1:0] min_start_ext;
      logic [AddrCalcWidth-1:0] max_start_ext;

      // Choose monotonically increasing starts with enough remaining address points for later ranges.
      min_start_ext = (i == 0) ? '0 : AddrCalcWidth'(range_start_addr[i-1]) + 1'b1;
      max_start_ext = addr_space_size - AddrCalcWidth'(NumBranchRanges - i);
      range_start_addr[i] =
          random_addr(AxilAddrWidth'(min_start_ext), AxilAddrWidth'(max_start_ext));
    end

    for (int i = 0; i < NumBranchRanges; i++) begin
      logic [AxilAddrWidth-1:0] max_end_addr;

      branch_start_addr[i] = range_start_addr[i];
      max_end_addr = (i == NumBranchRanges - 1) ? MaxBranchRangeAddr : range_start_addr[i+1] - 1'b1;
      branch_end_addr[i] = random_addr(branch_start_addr[i], max_end_addr);
    end
  endtask

  task automatic init_overlap_ranges(input logic [AddrCalcWidth-1:0] addr_space_size);
    if (addr_space_size < AddrCalcWidth'(2)) begin
      td.check(1'b0, "AXI-Lite address space cannot fit non-empty overlapping branch ranges");
      init_empty_ranges();
      return;
    end

    for (int i = 0; i < NumBranchRanges; i++) begin
      logic [AxilAddrWidth-1:0] max_start_addr;

      // Overlapping ranges can reuse address space, but each start must leave room for end > start.
      max_start_addr = AxilAddrWidth'(addr_space_size - AddrCalcWidth'(2));
      branch_start_addr[i] = random_addr(MinAxilAddr, max_start_addr);
      branch_end_addr[i] = random_addr(branch_start_addr[i] + 1'b1, MaxBranchRangeAddr);
    end

    if (NumBranchRanges > 1) begin
      int overlap_range_index = 1;

      // Force at least one deterministic overlap after random range generation so the overlap
      // scenario always exercises priority/normalization behavior.
      branch_start_addr[overlap_range_index] =
          random_addr(branch_start_addr[0] + 1'b1, branch_end_addr[0]);
      branch_end_addr[overlap_range_index] =
          random_addr(branch_start_addr[overlap_range_index], MaxBranchRangeAddr);
    end
  endtask

  task automatic init_ranges(input logic allow_overlap);
    logic [AddrCalcWidth-1:0] addr_space_size;

    // Leave the all-ones address outside branch space so every generated setup has at least one
    // guaranteed trunk address. Use widened math here to avoid wrapping when AxilAddrWidth is large.
    addr_space_size = (AddrCalcWidth'(1) << AxilAddrWidth) - 1'b1;
    if (allow_overlap) init_overlap_ranges(addr_space_size);
    else init_disjoint_ranges(addr_space_size);
    populate_addr_queues();
  endtask

  task automatic init_scenario(output axil_split_scenario_t scenario, input int num_writes,
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
    scenario.max_trunk_ready_stall_cycles = NoStallCycles;
    scenario.max_branch_ready_stall_cycles = NoStallCycles;
    scenario.allow_error_responses = 1'b0;
    scenario.force_trunk_route = 1'b0;
    scenario.force_branch_route = 1'b0;
    scenario.check_max_outstanding_reads = 1'b0;
    scenario.check_max_outstanding_writes = 1'b0;
  endtask

  task automatic init_idle();
    root_driver.init_idle();
    trunk_target.init_idle();
    branch_target.init_idle();
    root_monitor.init_idle();
    trunk_monitor.init_idle();
    branch_monitor.init_idle();
    scoreboard.init_idle();
    timeout_failed = 1'b0;
    num_trunk_writes = 0;
    num_trunk_reads = 0;
    num_branch_writes = 0;
    num_branch_reads = 0;
    init_ranges(.allow_overlap(1'b0));
  endtask

  function automatic logic [AxilAddrWidth-1:0] addr_for_route(input axil_split_route_t route,
                                                              input logic is_write);
    int branch_queue_index = is_write ? num_branch_writes : num_branch_reads;
    int trunk_queue_index = is_write ? num_trunk_writes : num_trunk_reads;

    if (route == AxilSplitRouteBranch)
      addr_for_route = branch_addr_q[branch_queue_index%branch_addr_q.size()];
    else addr_for_route = trunk_addr_q[trunk_queue_index%trunk_addr_q.size()];
  endfunction

  function automatic logic [AxilAddrWidth-1:0] fallback_trunk_addr();
    fallback_trunk_addr = addr_for_route(AxilSplitRouteTrunk, 1'b1);
  endfunction

  function automatic axil_b_t random_b_response(input logic allow_error);
    axi_resp_t response_choice;

    `BR_SIM_RANDOMIZE((response_choice), "AXI response choice");
    random_b_response = '0;
    random_b_response.resp = allow_error ? response_choice : AxiRespOkay;
  endfunction

  function automatic axil_b_t b_response(input logic [AxiRespWidth-1:0] resp);
    b_response = '0;
    b_response.resp = resp;
  endfunction

  function automatic axil_r_t random_r_response(input logic allow_error);
    logic [AxilDataWidth-1:0] data;
    logic [AxilUserWidth-1:0] user;
    axi_resp_t response_choice;

    `BR_SIM_RANDOMIZE((response_choice), "AXI response choice");
    `BR_SIM_RANDOMIZE((data), "AXI-Lite R data");
    `BR_SIM_RANDOMIZE((user), "AXI-Lite R user");
    random_r_response = '0;
    random_r_response.data = data;
    random_r_response.resp = allow_error ? response_choice : AxiRespOkay;
    random_r_response.user = user;
  endfunction

  function automatic axil_r_t r_response(input logic [AxiRespWidth-1:0] resp);
    logic [AxilDataWidth-1:0] data;
    logic [AxilUserWidth-1:0] user;

    `BR_SIM_RANDOMIZE((data), "AXI-Lite R data");
    `BR_SIM_RANDOMIZE((user), "AXI-Lite R user");
    r_response = '0;
    r_response.data = data;
    r_response.resp = resp;
    r_response.user = user;
  endfunction

  task automatic queue_write_addr_response(
      input axil_split_scenario_t scenario, input axil_split_route_t route,
      input logic [AxilAddrWidth-1:0] addr, input logic [AxilStrobeWidth-1:0] strb,
      input axil_b_t response);
    logic [AxiProtWidth-1:0] prot;
    logic [AxilUserWidth-1:0] awuser;
    logic [AxilDataWidth-1:0] data;
    logic [AxilUserWidth-1:0] wuser;
    int aw_gap_cycles = $urandom_range(scenario.max_aw_gap_cycles, scenario.min_aw_gap_cycles);
    int w_gap_cycles = $urandom_range(scenario.max_w_gap_cycles, scenario.min_w_gap_cycles);
    int b_stall_cycles = $urandom_range(scenario.max_b_stall_cycles, scenario.min_b_stall_cycles);

    `BR_SIM_RANDOMIZE((prot, awuser, data, wuser), "AXI-Lite write payload");
    root_driver.queue_write_user(addr, prot, awuser, data, strb, wuser, aw_gap_cycles, w_gap_cycles,
                                 b_stall_cycles);
    if (route == AxilSplitRouteBranch) begin
      branch_target.queue_b_response(response);
      num_branch_writes++;
    end else begin
      trunk_target.queue_b_response(response);
      num_trunk_writes++;
    end
  endtask

  task automatic queue_write_addr(input axil_split_scenario_t scenario,
                                  input axil_split_route_t route,
                                  input logic [AxilAddrWidth-1:0] addr);
    axil_b_t response = random_b_response(scenario.allow_error_responses);
    logic [AxilStrobeWidth-1:0] strb;

    `BR_SIM_RANDOMIZE((strb), "AXI-Lite write strobe");
    queue_write_addr_response(scenario, route, addr, strb, response);
  endtask

  task automatic queue_write(input axil_split_scenario_t scenario, input axil_split_route_t route);
    logic [AxilAddrWidth-1:0] addr = addr_for_route(route, 1'b1);

    queue_write_addr(scenario, route, addr);
  endtask

  task automatic queue_write_strobe(input axil_split_scenario_t scenario,
                                    input axil_split_route_t route,
                                    input logic [AxilStrobeWidth-1:0] strb);
    logic [AxilAddrWidth-1:0] addr = addr_for_route(route, 1'b1);
    axil_b_t response = random_b_response(scenario.allow_error_responses);

    queue_write_addr_response(scenario, route, addr, strb, response);
  endtask

  task automatic queue_write_response(input axil_split_scenario_t scenario,
                                      input axil_split_route_t route, input axil_b_t response);
    logic [  AxilAddrWidth-1:0] addr = addr_for_route(route, 1'b1);
    logic [AxilStrobeWidth-1:0] strb;

    `BR_SIM_RANDOMIZE((strb), "AXI-Lite write strobe");
    queue_write_addr_response(scenario, route, addr, strb, response);
  endtask

  task automatic queue_read_addr_response(
      input axil_split_scenario_t scenario, input axil_split_route_t route,
      input logic [AxilAddrWidth-1:0] addr, input axil_r_t response);
    logic [AxiProtWidth-1:0] prot;
    logic [AxilUserWidth-1:0] aruser;
    int ar_gap_cycles = $urandom_range(scenario.max_ar_gap_cycles, scenario.min_ar_gap_cycles);
    int r_stall_cycles = $urandom_range(scenario.max_r_stall_cycles, scenario.min_r_stall_cycles);

    `BR_SIM_RANDOMIZE((prot, aruser), "AXI-Lite read request payload");
    root_driver.queue_read_user(addr, prot, aruser, ar_gap_cycles, r_stall_cycles);
    if (route == AxilSplitRouteBranch) begin
      branch_target.queue_r_response(response);
      num_branch_reads++;
    end else begin
      trunk_target.queue_r_response(response);
      num_trunk_reads++;
    end
  endtask

  task automatic queue_read_addr(input axil_split_scenario_t scenario,
                                 input axil_split_route_t route,
                                 input logic [AxilAddrWidth-1:0] addr);
    queue_read_addr_response(scenario, route, addr, random_r_response(scenario.allow_error_responses
                             ));
  endtask

  task automatic queue_read(input axil_split_scenario_t scenario, input axil_split_route_t route);
    logic [AxilAddrWidth-1:0] addr = addr_for_route(route, 1'b0);

    queue_read_addr(scenario, route, addr);
  endtask

  task automatic queue_read_response(input axil_split_scenario_t scenario,
                                     input axil_split_route_t route, input axil_r_t response);
    logic [AxilAddrWidth-1:0] addr = addr_for_route(route, 1'b0);

    queue_read_addr_response(scenario, route, addr, response);
  endtask

  task automatic queue_mixed_transactions(input axil_split_scenario_t scenario);
    int remaining_writes = scenario.num_writes;
    int remaining_reads = scenario.num_reads;

    while (remaining_writes != 0 || remaining_reads != 0) begin
      axil_split_route_t route;
      logic is_write;

      if (scenario.force_branch_route) route = AxilSplitRouteBranch;
      else if (scenario.force_trunk_route) route = AxilSplitRouteTrunk;
      else `BR_SIM_RANDOMIZE((route), "AXI-Lite split route");

      if (remaining_reads == 0) is_write = 1'b1;
      else if (remaining_writes == 0) is_write = 1'b0;
      else is_write = $urandom_range(1, 0);

      if (is_write) begin
        queue_write(scenario, route);
        remaining_writes--;
      end else begin
        queue_read(scenario, route);
        remaining_reads--;
      end
    end
  endtask

  task automatic collect_scoreboard_observations();
    axil_aw_observation_t root_aw_q[$];
    axil_w_observation_t root_w_q[$];
    axil_ar_observation_t root_ar_q[$];
    axil_b_observation_t root_b_q[$];
    axil_r_observation_t root_r_q[$];
    axil_aw_observation_t trunk_aw_q[$];
    axil_w_observation_t trunk_w_q[$];
    axil_ar_observation_t trunk_ar_q[$];
    axil_b_observation_t trunk_b_q[$];
    axil_r_observation_t trunk_r_q[$];
    axil_aw_observation_t branch_aw_q[$];
    axil_w_observation_t branch_w_q[$];
    axil_ar_observation_t branch_ar_q[$];
    axil_b_observation_t branch_b_q[$];
    axil_r_observation_t branch_r_q[$];

    root_monitor.get_observed_request_observations(root_aw_q, root_w_q, root_ar_q);
    root_monitor.get_observed_response_observations(root_b_q, root_r_q);
    trunk_monitor.get_observed_request_observations(trunk_aw_q, trunk_w_q, trunk_ar_q);
    trunk_monitor.get_observed_response_observations(trunk_b_q, trunk_r_q);
    branch_monitor.get_observed_request_observations(branch_aw_q, branch_w_q, branch_ar_q);
    branch_monitor.get_observed_response_observations(branch_b_q, branch_r_q);
    scoreboard.set_root_observations(root_aw_q, root_w_q, root_ar_q, root_b_q, root_r_q);
    scoreboard.set_trunk_observations(trunk_aw_q, trunk_w_q, trunk_ar_q, trunk_b_q, trunk_r_q);
    scoreboard.set_branch_observations(branch_aw_q, branch_w_q, branch_ar_q, branch_b_q,
                                       branch_r_q);
  endtask

  task automatic run_queued_scenario(input string scenario_name,
                                     input axil_split_scenario_t scenario);
    int expected_max_reads = scenario.check_max_outstanding_reads ? MaxOutstandingReads : 0;
    int expected_max_writes = scenario.check_max_outstanding_writes ? MaxOutstandingWrites : 0;

    $display("Running br_amba_axil_split scenario: %s", scenario_name);
    fork
      begin
        fork
          root_driver.run(scenario.num_writes, scenario.num_reads);
          trunk_target.run(num_trunk_writes, num_trunk_reads,
                           scenario.max_trunk_ready_stall_cycles);
          branch_target.run(num_branch_writes, num_branch_reads,
                            scenario.max_branch_ready_stall_cycles);
        join
        td.wait_cycles(1);
      end
      root_monitor.run();
      trunk_monitor.run();
      branch_monitor.run();
      timeout(timeout_tick, TimeoutCycles, $sformatf(
              "Timeout waiting for br_amba_axil_split scenario %s", scenario_name), timeout_failed);
    join_any
    disable fork;

    collect_scoreboard_observations();
    scoreboard.compare(scenario.num_writes, scenario.num_reads, expected_max_reads,
                       expected_max_writes, branch_start_addr, branch_end_addr);
    td.check(!root_driver_failed, "AXI-Lite root requester driver reported failure");
    td.check(!trunk_target_failed, "AXI-Lite trunk target driver reported failure");
    td.check(!branch_target_failed, "AXI-Lite branch target driver reported failure");
    td.check(!root_monitor_failed, "AXI-Lite root monitor reported failure");
    td.check(!trunk_monitor_failed, "AXI-Lite trunk monitor reported failure");
    td.check(!branch_monitor_failed, "AXI-Lite branch monitor reported failure");
    td.check(!scoreboard_failed, "AXI-Lite split scoreboard reported failure");
    td.check(!timeout_failed, "AXI-Lite split scenario timed out");
  endtask

  task automatic check_observed_count(input string scenario_name, input string channel_name,
                                      input int actual, input int expected);
    td.check_integer(actual, expected, $sformatf(
                     "%s pre-reset %s count mismatch", scenario_name, channel_name));
  endtask

  task automatic check_observed_axi_counts(
      input string scenario_name, input string interface_name, input int aw_actual,
      input int w_actual, input int ar_actual, input int b_actual, input int r_actual,
      input int aw_expected, input int w_expected, input int ar_expected, input int b_expected,
      input int r_expected);
    check_observed_count(scenario_name, {interface_name, " AW"}, aw_actual, aw_expected);
    check_observed_count(scenario_name, {interface_name, " W"}, w_actual, w_expected);
    check_observed_count(scenario_name, {interface_name, " AR"}, ar_actual, ar_expected);
    check_observed_count(scenario_name, {interface_name, " B"}, b_actual, b_expected);
    check_observed_count(scenario_name, {interface_name, " R"}, r_actual, r_expected);
  endtask

  task automatic check_reset_pre_reset_traffic(input string scenario_name,
                                               input axil_reset_counts_t expected);
    axil_aw_observation_t root_aw_q[$];
    axil_w_observation_t root_w_q[$];
    axil_ar_observation_t root_ar_q[$];
    axil_b_observation_t root_b_q[$];
    axil_r_observation_t root_r_q[$];
    axil_aw_observation_t trunk_aw_q[$];
    axil_w_observation_t trunk_w_q[$];
    axil_ar_observation_t trunk_ar_q[$];
    axil_b_observation_t trunk_b_q[$];
    axil_r_observation_t trunk_r_q[$];
    axil_aw_observation_t branch_aw_q[$];
    axil_w_observation_t branch_w_q[$];
    axil_ar_observation_t branch_ar_q[$];
    axil_b_observation_t branch_b_q[$];
    axil_r_observation_t branch_r_q[$];

    root_monitor.get_observed_request_observations(root_aw_q, root_w_q, root_ar_q);
    root_monitor.get_observed_response_observations(root_b_q, root_r_q);
    trunk_monitor.get_observed_request_observations(trunk_aw_q, trunk_w_q, trunk_ar_q);
    trunk_monitor.get_observed_response_observations(trunk_b_q, trunk_r_q);
    branch_monitor.get_observed_request_observations(branch_aw_q, branch_w_q, branch_ar_q);
    branch_monitor.get_observed_response_observations(branch_b_q, branch_r_q);

    check_observed_axi_counts(scenario_name, "root", root_aw_q.size(), root_w_q.size(),
                              root_ar_q.size(), root_b_q.size(), root_r_q.size(), expected.root_aw,
                              expected.root_w, expected.root_ar, expected.root_b, expected.root_r);
    check_observed_axi_counts(scenario_name, "trunk", trunk_aw_q.size(), trunk_w_q.size(),
                              trunk_ar_q.size(), trunk_b_q.size(), trunk_r_q.size(),
                              expected.trunk_aw, expected.trunk_w, expected.trunk_ar,
                              expected.trunk_b, expected.trunk_r);
    check_observed_axi_counts(scenario_name, "branch", branch_aw_q.size(), branch_w_q.size(),
                              branch_ar_q.size(), branch_b_q.size(), branch_r_q.size(),
                              expected.branch_aw, expected.branch_w, expected.branch_ar,
                              expected.branch_b, expected.branch_r);
    td.check(!root_monitor_failed, $sformatf(
             "%s root monitor reported failure before reset", scenario_name));
    td.check(!trunk_monitor_failed, $sformatf(
             "%s trunk monitor reported failure before reset", scenario_name));
    td.check(!branch_monitor_failed, $sformatf(
             "%s branch monitor reported failure before reset", scenario_name));
  endtask

  task automatic check_idle(input string check_context, input logic only_during_reset = 1'b0,
                            input logic check_root_responses = 1'b1);
    forever begin
      @(posedge clk);
      if (!only_during_reset || rst) begin
        td.check(!trunk_awvalid, $sformatf("%s: Trunk AWVALID asserted", check_context));
        td.check(!trunk_wvalid, $sformatf("%s: Trunk WVALID asserted", check_context));
        td.check(!trunk_arvalid, $sformatf("%s: Trunk ARVALID asserted", check_context));
        td.check(!branch_awvalid, $sformatf("%s: Branch AWVALID asserted", check_context));
        td.check(!branch_wvalid, $sformatf("%s: Branch WVALID asserted", check_context));
        td.check(!branch_arvalid, $sformatf("%s: Branch ARVALID asserted", check_context));
        if (check_root_responses) begin
          td.check(!root_bvalid, $sformatf("%s: Root BVALID asserted", check_context));
          td.check(!root_rvalid, $sformatf("%s: Root RVALID asserted", check_context));
        end
      end
    end
  endtask

  // Sample each post-reset edge so a one-cycle invalid VALID pulse cannot slip through.
  task automatic test_reset_idle();
    init_idle();
    td.reset_dut();
    fork
      td.wait_cycles(2);
      check_idle("Reset idle post-reset");
    join_any
    disable fork;
  endtask

  task automatic test_single_transaction(input string scenario_name, input axil_split_route_t route,
                                         input logic is_write);
    axil_split_scenario_t scenario;

    init_scenario(scenario, is_write ? SingleWrite : NoWrites, is_write ? NoReads : SingleRead);
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route  = route == AxilSplitRouteTrunk;
    init_idle();
    if (is_write) queue_write(scenario, route);
    else queue_read(scenario, route);
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic test_range_boundaries();
    localparam int BoundaryTransactionsPerRange = 4;

    axil_split_scenario_t scenario;

    init_scenario(scenario, NumBranchRanges * BoundaryTransactionsPerRange,
                  NumBranchRanges * BoundaryTransactionsPerRange);
    init_idle();
    for (int i = 0; i < NumBranchRanges; i++) begin
      logic [AxilAddrWidth-1:0] trunk_below_addr;
      logic [AxilAddrWidth-1:0] trunk_above_addr;

      queue_write_addr(scenario, AxilSplitRouteBranch, branch_start_addr[i]);
      queue_read_addr(scenario, AxilSplitRouteBranch, branch_start_addr[i]);
      queue_write_addr(scenario, AxilSplitRouteBranch, branch_end_addr[i]);
      queue_read_addr(scenario, AxilSplitRouteBranch, branch_end_addr[i]);

      trunk_below_addr = branch_start_addr[i] - AxilAddrWidth'(1);
      if (branch_start_addr[i] == MinAxilAddr || is_branch_addr(trunk_below_addr))
        trunk_below_addr = fallback_trunk_addr();
      queue_write_addr(scenario, AxilSplitRouteTrunk, trunk_below_addr);
      queue_read_addr(scenario, AxilSplitRouteTrunk, trunk_below_addr);

      trunk_above_addr = branch_end_addr[i] + AxilAddrWidth'(1);
      if (branch_end_addr[i] == MaxAxilAddr || is_branch_addr(trunk_above_addr))
        trunk_above_addr = fallback_trunk_addr();
      queue_write_addr(scenario, AxilSplitRouteTrunk, trunk_above_addr);
      queue_read_addr(scenario, AxilSplitRouteTrunk, trunk_above_addr);
    end
    run_queued_scenario("range_boundaries", scenario);
  endtask

  // Force a controlled partial overlap while keeping start <= end.
  task automatic test_overlapping_branch_ranges();
    axil_split_scenario_t scenario;
    int overlap_range_index = 1;
    logic [AxilAddrWidth-1:0] overlap_addr;

    if (NumBranchRanges < 2) return;

    init_scenario(scenario, SingleWrite, SingleRead);
    init_idle();
    init_ranges(.allow_overlap(1'b1));
    overlap_addr = branch_start_addr[overlap_range_index];
    queue_write_addr(scenario, AxilSplitRouteBranch, overlap_addr);
    queue_read_addr(scenario, AxilSplitRouteBranch, overlap_addr);
    run_queued_scenario("overlapping_branch_ranges", scenario);
  endtask

  // The RTL does not enforce the static-range contract, so document current idle reconfiguration.
  task automatic test_unsupported_idle_range_reconfigure();
    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, SingleRead);
    scenario.force_branch_route = 1'b1;
    init_idle();
    td.reset_dut();
    branch_start_addr[0] = MinAxilAddr;
    branch_end_addr[0]   = MinAxilAddr + AxilAddrWidth'(1);
    populate_addr_queues();
    queue_write(scenario, AxilSplitRouteBranch);
    queue_read(scenario, AxilSplitRouteBranch);
    run_queued_scenario("unsupported_idle_range_reconfigure", scenario);
  endtask

  task automatic test_multi_range_routing();
    axil_split_scenario_t scenario;

    init_scenario(scenario, NumBranchRanges * 2, NumBranchRanges * 2);
    init_idle();
    for (int i = 0; i < NumBranchRanges; i++) begin
      queue_write(scenario, AxilSplitRouteBranch);
      queue_write(scenario, AxilSplitRouteTrunk);
      queue_read(scenario, AxilSplitRouteBranch);
      queue_read(scenario, AxilSplitRouteTrunk);
    end
    run_queued_scenario("multi_range_routing", scenario);
  endtask

  task automatic test_write_channel_skew(input string scenario_name, input int aw_gap_cycles,
                                         input int w_gap_cycles);
    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, NoReads);
    scenario.min_aw_gap_cycles = aw_gap_cycles;
    scenario.max_aw_gap_cycles = aw_gap_cycles;
    scenario.min_w_gap_cycles  = w_gap_cycles;
    scenario.max_w_gap_cycles  = w_gap_cycles;
    init_idle();
    queue_write(scenario, AxilSplitRouteBranch);
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic test_write_address_before_data();
    test_write_channel_skew("write_address_before_data", NoGapCycles, WriteSkewGapCycles);
  endtask

  task automatic test_write_data_before_address();
    test_write_channel_skew("write_data_before_address", WriteSkewGapCycles, NoGapCycles);
  endtask

  task automatic test_zero_strobe_write();
    localparam logic [AxilStrobeWidth-1:0] ZeroStrobe = '0;

    axil_split_scenario_t scenario;

    init_scenario(scenario, 2, NoReads);
    init_idle();
    queue_write_strobe(scenario, AxilSplitRouteTrunk, ZeroStrobe);
    queue_write_strobe(scenario, AxilSplitRouteBranch, ZeroStrobe);
    run_queued_scenario("zero_strobe_write", scenario);
  endtask

  task automatic test_request_sidebands_and_resp_types();
    localparam int NumResponseTypes = 2 ** AxiRespWidth;

    axi_resp_t responses[NumResponseTypes] = '{
        AxiRespOkay,
        AxiRespExOkay,
        AxiRespSlverr,
        AxiRespDecerr
    };
    axil_split_scenario_t scenario;

    init_scenario(scenario, NumResponseTypes * 2, NumResponseTypes * 2);
    init_idle();
    foreach (responses[i]) begin
      queue_write_response(scenario, AxilSplitRouteTrunk, b_response(responses[i]));
      queue_write_response(scenario, AxilSplitRouteBranch, b_response(responses[i]));
      queue_read_response(scenario, AxilSplitRouteTrunk, r_response(responses[i]));
      queue_read_response(scenario, AxilSplitRouteBranch, r_response(responses[i]));
    end
    run_queued_scenario("request_sidebands_and_resp_types", scenario);
  endtask

  task automatic test_route_switch_blocked_by_outstanding(input string scenario_name,
                                                          input logic is_write);
    localparam int RouteSwitchTransactions = 4;
    localparam int RouteSwitchResponseStallCycles = 4;

    axil_split_scenario_t scenario;

    init_scenario(scenario, is_write ? RouteSwitchTransactions : NoWrites,
                  is_write ? NoReads : RouteSwitchTransactions);
    if (is_write) begin
      scenario.min_b_stall_cycles = RouteSwitchResponseStallCycles;
      scenario.max_b_stall_cycles = RouteSwitchResponseStallCycles;
    end else begin
      scenario.min_r_stall_cycles = RouteSwitchResponseStallCycles;
      scenario.max_r_stall_cycles = RouteSwitchResponseStallCycles;
    end
    init_idle();
    for (int i = 0; i < RouteSwitchTransactions; i++) begin
      axil_split_route_t route = (i % 2 == 0) ? AxilSplitRouteBranch : AxilSplitRouteTrunk;

      if (is_write) queue_write(scenario, route);
      else queue_read(scenario, route);
    end
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic check_read_pending_write_route_independence(input string scenario_name);
    axil_aw_observation_t trunk_aw_q[$];
    axil_w_observation_t trunk_w_q[$];
    axil_ar_observation_t trunk_ar_q[$];
    axil_b_observation_t branch_b_q[$];
    axil_r_observation_t branch_r_q[$];
    logic observed_expected_events;
    time trunk_write_request_ts;

    trunk_monitor.get_observed_request_observations(trunk_aw_q, trunk_w_q, trunk_ar_q);
    branch_monitor.get_observed_response_observations(branch_b_q, branch_r_q);
    observed_expected_events = trunk_aw_q.size() != 0 && trunk_w_q.size() != 0 &&
        branch_r_q.size() != 0;
    td.check(observed_expected_events, $sformatf(
             "%s did not observe expected trunk write and branch R", scenario_name));
    if (observed_expected_events) begin
      trunk_write_request_ts = `BR_SIM_MAX(trunk_aw_q[0].timestamp, trunk_w_q[0].timestamp);
      td.check(trunk_write_request_ts < branch_r_q[0].timestamp, $sformatf(
               "%s trunk write waited for branch read response", scenario_name));
    end
  endtask

  task automatic check_write_pending_read_route_independence(input string scenario_name);
    axil_aw_observation_t trunk_aw_q[$];
    axil_w_observation_t trunk_w_q[$];
    axil_ar_observation_t trunk_ar_q[$];
    axil_b_observation_t branch_b_q[$];
    axil_r_observation_t branch_r_q[$];
    logic observed_expected_events;

    trunk_monitor.get_observed_request_observations(trunk_aw_q, trunk_w_q, trunk_ar_q);
    branch_monitor.get_observed_response_observations(branch_b_q, branch_r_q);
    observed_expected_events = trunk_ar_q.size() != 0 && branch_b_q.size() != 0;
    td.check(observed_expected_events, $sformatf(
             "%s did not observe expected trunk read and branch B", scenario_name));
    if (observed_expected_events) begin
      td.check(trunk_ar_q[0].timestamp < branch_b_q[0].timestamp, $sformatf(
               "%s trunk read waited for branch write response", scenario_name));
    end
  endtask

  task automatic test_read_pending_write_other_route();
    string scenario_name = "read_pending_write_other_route";
    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, SingleRead);
    scenario.min_r_stall_cycles = OutstandingResponseStallCycles;
    scenario.max_r_stall_cycles = OutstandingResponseStallCycles;
    init_idle();
    queue_read(scenario, AxilSplitRouteBranch);
    queue_write(scenario, AxilSplitRouteTrunk);
    run_queued_scenario(scenario_name, scenario);
    check_read_pending_write_route_independence(scenario_name);
  endtask

  task automatic test_write_pending_read_other_route();
    string scenario_name = "write_pending_read_other_route";
    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, SingleRead);
    scenario.min_b_stall_cycles = OutstandingResponseStallCycles;
    scenario.max_b_stall_cycles = OutstandingResponseStallCycles;
    init_idle();
    queue_write(scenario, AxilSplitRouteBranch);
    queue_read(scenario, AxilSplitRouteTrunk);
    run_queued_scenario(scenario_name, scenario);
    check_write_pending_read_route_independence(scenario_name);
  endtask

  task automatic test_max_outstanding_reads(input string scenario_name,
                                            input axil_split_route_t route);
    axil_split_scenario_t scenario;

    init_scenario(scenario, NoWrites, MaxOutstandingReads + 2);
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route = route == AxilSplitRouteTrunk;
    scenario.min_r_stall_cycles = OutstandingResponseStallCycles;
    scenario.max_r_stall_cycles = OutstandingResponseStallCycles;
    scenario.check_max_outstanding_reads = 1'b1;
    init_idle();
    queue_mixed_transactions(scenario);
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic test_max_outstanding_writes(input string scenario_name,
                                             input axil_split_route_t route);
    axil_split_scenario_t scenario;

    init_scenario(scenario, MaxOutstandingWrites + 2, NoReads);
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route = route == AxilSplitRouteTrunk;
    scenario.min_b_stall_cycles = OutstandingResponseStallCycles;
    scenario.max_b_stall_cycles = OutstandingResponseStallCycles;
    scenario.check_max_outstanding_writes = 1'b1;
    init_idle();
    queue_mixed_transactions(scenario);
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic test_route_backpressure(input string scenario_name,
                                         input axil_split_route_t route);
    localparam int BackpressureReadyStallCycles = 3;

    axil_split_scenario_t scenario;

    init_scenario(scenario, $urandom_range(MaxDirectedTransactions, MinDirectedTransactions),
                  $urandom_range(MaxDirectedTransactions, MinDirectedTransactions));
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route  = route == AxilSplitRouteTrunk;
    if (route == AxilSplitRouteBranch)
      scenario.max_branch_ready_stall_cycles = BackpressureReadyStallCycles;
    else scenario.max_trunk_ready_stall_cycles = BackpressureReadyStallCycles;
    init_idle();
    queue_mixed_transactions(scenario);
    run_queued_scenario(scenario_name, scenario);
  endtask

  task automatic test_mixed_random_traffic();
    axil_split_scenario_t scenario;

    init_scenario(scenario, $urandom_range(MaxDirectedTransactions, MinDirectedTransactions),
                  $urandom_range(MaxDirectedTransactions, MinDirectedTransactions));
    scenario.min_aw_gap_cycles = $urandom_range(MaxRandomDelayCycles, MinRandomDelayCycles);
    scenario.max_aw_gap_cycles = $urandom_range(MaxRandomDelayCycles, scenario.min_aw_gap_cycles);
    scenario.min_w_gap_cycles = $urandom_range(MaxRandomDelayCycles, MinRandomDelayCycles);
    scenario.max_w_gap_cycles = $urandom_range(MaxRandomDelayCycles, scenario.min_w_gap_cycles);
    scenario.min_ar_gap_cycles = $urandom_range(MaxRandomDelayCycles, MinRandomDelayCycles);
    scenario.max_ar_gap_cycles = $urandom_range(MaxRandomDelayCycles, scenario.min_ar_gap_cycles);
    scenario.min_b_stall_cycles = $urandom_range(MaxRandomDelayCycles, MinRandomDelayCycles);
    scenario.max_b_stall_cycles = $urandom_range(MaxRandomDelayCycles, scenario.min_b_stall_cycles);
    scenario.min_r_stall_cycles = $urandom_range(MaxRandomDelayCycles, MinRandomDelayCycles);
    scenario.max_r_stall_cycles = $urandom_range(MaxRandomDelayCycles, scenario.min_r_stall_cycles);
    scenario.allow_error_responses = 1'b1;
    init_idle();
    queue_mixed_transactions(scenario);
    run_queued_scenario("mixed_random_traffic", scenario);
  endtask

  task automatic test_stress();
    localparam int MinStressTransactions = 256;
    localparam int MaxStressTransactions = 512;

    axil_split_scenario_t scenario;

    init_scenario(scenario, $urandom_range(MaxStressTransactions, MinStressTransactions),
                  $urandom_range(MaxStressTransactions, MinStressTransactions));
    scenario.allow_error_responses = 1'b1;
    init_idle();
    queue_mixed_transactions(scenario);
    run_queued_scenario("stress", scenario);
  endtask

  task automatic run_reset_recovery(input string scenario_name);
    axil_split_scenario_t scenario;

    init_idle();
    init_scenario(scenario, SingleWrite, SingleRead);
    queue_mixed_transactions(scenario);
    run_queued_scenario(scenario_name, scenario);
  endtask

  function automatic string reset_trigger_name(input axil_reset_trigger_t trigger);
    case (trigger)
      AxilResetTriggerAwBeforeW: reset_trigger_name = "AW-before-W";
      AxilResetTriggerWBeforeAw: reset_trigger_name = "W-before-AW";
      AxilResetTriggerBPending:  reset_trigger_name = "pending B";
      AxilResetTriggerRPending:  reset_trigger_name = "pending R";
      default:                   reset_trigger_name = "unknown";
    endcase
  endfunction

  function automatic string route_name(input axil_split_route_t route);
    if (route == AxilSplitRouteBranch) route_name = "branch";
    else route_name = "trunk";
  endfunction

  task automatic run_pre_reset_target(input axil_split_route_t route);
    if (route == AxilSplitRouteBranch)
      branch_target.run(num_branch_writes, num_branch_reads, NoStallCycles);
    else trunk_target.run(num_trunk_writes, num_trunk_reads, NoStallCycles);
  endtask

  task automatic wait_for_reset_trigger(input axil_reset_trigger_t trigger);
    @(posedge clk);
    unique case (trigger)
      AxilResetTriggerAwBeforeW: begin
        while (!(root_awvalid && !root_wvalid)) @(posedge clk);
        td.check(root_awvalid && !root_wvalid,
                 "AW-before-W reset did not reach AWVALID-before-WVALID phase");
      end
      AxilResetTriggerWBeforeAw: begin
        while (!(root_wvalid && !root_awvalid)) @(posedge clk);
        td.check(root_wvalid && !root_awvalid,
                 "W-before-AW reset did not reach WVALID-before-AWVALID phase");
      end
      AxilResetTriggerBPending: begin
        while (!(root_bvalid && !root_bready)) @(posedge clk);
      end
      AxilResetTriggerRPending: begin
        while (!(root_rvalid && !root_rready)) @(posedge clk);
      end
    endcase
    td.reset_dut();
  endtask

  task automatic run_reset_scenario(
      input string scenario_name, input string recovery_name, input axil_split_scenario_t scenario,
      input axil_reset_trigger_t trigger, input logic check_pre_reset,
      input axil_split_route_t route, input axil_reset_counts_t expected_counts);
    if (check_pre_reset) begin
      fork : pre_reset_observation_threads
        run_pre_reset_target(route);
        root_monitor.run();
        trunk_monitor.run();
        branch_monitor.run();
      join_none
    end
    fork
      root_driver.run(scenario.num_writes, scenario.num_reads);
      wait_for_reset_trigger(trigger);
      timeout(timeout_tick, MidResetTimeoutCycles, $sformatf(
              "Timeout waiting for %s reset trigger", reset_trigger_name(trigger)), timeout_failed);
    join_any
    disable fork;
    if (check_pre_reset) disable pre_reset_observation_threads;
    td.check(!timeout_failed, $sformatf("%s reset trigger timed out", reset_trigger_name(trigger)));
    if (check_pre_reset) check_reset_pre_reset_traffic(scenario_name, expected_counts);
    run_reset_recovery(recovery_name);
  endtask

  task automatic test_reset_write_before_data();
    localparam int MidResetWriteDataGapCycles = 8;

    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, NoReads);
    scenario.force_branch_route = 1'b1;
    scenario.min_w_gap_cycles   = MidResetWriteDataGapCycles;
    scenario.max_w_gap_cycles   = MidResetWriteDataGapCycles;
    init_idle();
    queue_write(scenario, AxilSplitRouteBranch);
    // This reset point intentionally occurs before an AW/W pair can handshake downstream.
    run_reset_scenario("AW-before-W reset", "reset_write_before_data_recovery", scenario,
                       AxilResetTriggerAwBeforeW, 1'b0, AxilSplitRouteBranch, '{default: 0});
  endtask

  task automatic test_reset_write_data_before_address();
    localparam int MidResetWriteAddrGapCycles = 8;

    axil_split_scenario_t scenario;

    init_scenario(scenario, SingleWrite, NoReads);
    scenario.force_branch_route = 1'b1;
    scenario.min_aw_gap_cycles  = MidResetWriteAddrGapCycles;
    scenario.max_aw_gap_cycles  = MidResetWriteAddrGapCycles;
    init_idle();
    queue_write(scenario, AxilSplitRouteBranch);
    // This reset point intentionally occurs before an AW/W pair can handshake downstream.
    run_reset_scenario("W-before-AW reset", "reset_write_data_before_address_recovery", scenario,
                       AxilResetTriggerWBeforeAw, 1'b0, AxilSplitRouteBranch, '{default: 0});
  endtask

  task automatic test_reset_write_response_pending(input axil_split_route_t route);
    axil_split_scenario_t scenario;
    axil_reset_counts_t   expected_counts = '{default: 0, root_aw: 1, root_w: 1};

    if (route == AxilSplitRouteBranch) begin
      expected_counts.branch_aw = 1;
      expected_counts.branch_w  = 1;
    end else begin
      expected_counts.trunk_aw = 1;
      expected_counts.trunk_w  = 1;
    end

    init_scenario(scenario, SingleWrite, NoReads);
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route  = route == AxilSplitRouteTrunk;
    scenario.min_b_stall_cycles = MidResetResponseStallCycles;
    scenario.max_b_stall_cycles = MidResetResponseStallCycles;
    init_idle();
    queue_write(scenario, route);
    run_reset_scenario($sformatf("%s pending B reset", route_name(route)), $sformatf(
                       "reset_%s_write_response_pending_recovery", route_name(route)), scenario,
                       AxilResetTriggerBPending, 1'b1, route, expected_counts);
  endtask

  task automatic test_reset_read_response_pending(input axil_split_route_t route);
    axil_split_scenario_t scenario;
    axil_reset_counts_t   expected_counts = '{default: 0, root_ar: 1};

    if (route == AxilSplitRouteBranch) expected_counts.branch_ar = 1;
    else expected_counts.trunk_ar = 1;

    init_scenario(scenario, NoWrites, SingleRead);
    scenario.force_branch_route = route == AxilSplitRouteBranch;
    scenario.force_trunk_route  = route == AxilSplitRouteTrunk;
    scenario.min_r_stall_cycles = MidResetResponseStallCycles;
    scenario.max_r_stall_cycles = MidResetResponseStallCycles;
    init_idle();
    queue_read(scenario, route);
    run_reset_scenario($sformatf("%s pending R reset", route_name(route)), $sformatf(
                       "reset_%s_read_response_pending_recovery", route_name(route)), scenario,
                       AxilResetTriggerRPending, 1'b1, route, expected_counts);
  endtask

  initial begin
    wait (reset_monitor_enabled);
    // The RTL reset contract only guarantees routed request outputs stay idle during reset.
    check_idle("During reset", .only_during_reset(1'b1), .check_root_responses(1'b0));
  end

  initial begin
    init_idle();
    reset_monitor_enabled = 1'b1;
    td.reset_dut();
    test_reset_idle();
    test_single_transaction("trunk_write_no_delay", AxilSplitRouteTrunk, 1'b1);
    test_single_transaction("trunk_read_no_delay", AxilSplitRouteTrunk, 1'b0);
    test_single_transaction("branch_write_no_delay", AxilSplitRouteBranch, 1'b1);
    test_single_transaction("branch_read_no_delay", AxilSplitRouteBranch, 1'b0);
    test_range_boundaries();
    test_overlapping_branch_ranges();
    test_unsupported_idle_range_reconfigure();
    test_multi_range_routing();
    test_write_address_before_data();
    test_write_data_before_address();
    test_zero_strobe_write();
    test_request_sidebands_and_resp_types();
    test_route_switch_blocked_by_outstanding("read_route_switch_blocked_by_outstanding", 1'b0);
    test_route_switch_blocked_by_outstanding("write_route_switch_blocked_by_outstanding", 1'b1);
    test_read_pending_write_other_route();
    test_write_pending_read_other_route();
    test_max_outstanding_reads("branch_max_outstanding_reads", AxilSplitRouteBranch);
    test_max_outstanding_reads("trunk_max_outstanding_reads", AxilSplitRouteTrunk);
    test_max_outstanding_writes("branch_max_outstanding_writes", AxilSplitRouteBranch);
    test_max_outstanding_writes("trunk_max_outstanding_writes", AxilSplitRouteTrunk);
    test_route_backpressure("trunk_backpressure", AxilSplitRouteTrunk);
    test_route_backpressure("branch_backpressure", AxilSplitRouteBranch);
    test_mixed_random_traffic();
    test_stress();
    test_reset_write_before_data();
    test_reset_write_data_before_address();
    test_reset_write_response_pending(AxilSplitRouteBranch);
    test_reset_write_response_pending(AxilSplitRouteTrunk);
    test_reset_read_response_pending(AxilSplitRouteBranch);
    test_reset_read_response_pending(AxilSplitRouteTrunk);
    td.finish();
  end
endmodule : br_amba_axil_split_tb
