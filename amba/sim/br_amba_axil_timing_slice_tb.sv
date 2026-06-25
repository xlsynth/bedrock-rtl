// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;

typedef struct {
  int num_writes;
  int num_reads;
  int valid_gap_cycles;
  int max_stall_cycles;
} axil_timing_slice_controls_t;

// Directed simulation testbench for br_amba_axil_timing_slice.
//
// Scope:
// - checks reset-visible AXI-Lite channel valid outputs are idle;
// - sends deterministic payloads on all five independent AXI-Lite channels;
// - checks output payload order and data integrity under channel backpressure;
// - sweeps address width, data width, and transaction count from Bazel.
module br_amba_axil_timing_slice_tb;
  parameter int AddrWidth = 12;
  parameter int DataWidth = 32;
  parameter int AWUserWidth = 2;
  parameter int WUserWidth = 2;
  parameter int ARUserWidth = 2;
  parameter int RUserWidth = 2;
  parameter int BUserWidth = 2;
  parameter int NumTransactions = 10;

  localparam int StrobeWidth = DataWidth / 8;
  localparam int TimeoutCycles = (NumTransactions * 80) + 400;
  localparam int DirectedValidGapCycles = 0;
  localparam int DirectedStallCycles = 3;
  localparam int RandomizedValidGapCycles = 1;
  localparam int RandomizedStallCycles = 0;
  localparam int PayloadSeed = 32'h2468_1357;

  logic clk;
  logic rst;
  logic driver_failed;
  logic monitor_failed;

  logic [AddrWidth-1:0] target_awaddr;
  logic [AxiProtWidth-1:0] target_awprot;
  logic [AWUserWidth-1:0] target_awuser;
  logic target_awvalid;
  logic target_awready;
  logic [DataWidth-1:0] target_wdata;
  logic [StrobeWidth-1:0] target_wstrb;
  logic [WUserWidth-1:0] target_wuser;
  logic target_wvalid;
  logic target_wready;
  logic [AxiRespWidth-1:0] target_bresp;
  logic [BUserWidth-1:0] target_buser;
  logic target_bvalid;
  logic target_bready;
  logic [AddrWidth-1:0] target_araddr;
  logic [AxiProtWidth-1:0] target_arprot;
  logic [ARUserWidth-1:0] target_aruser;
  logic target_arvalid;
  logic target_arready;
  logic [DataWidth-1:0] target_rdata;
  logic [AxiRespWidth-1:0] target_rresp;
  logic [RUserWidth-1:0] target_ruser;
  logic target_rvalid;
  logic target_rready;

  logic [AddrWidth-1:0] init_awaddr;
  logic [AxiProtWidth-1:0] init_awprot;
  logic [AWUserWidth-1:0] init_awuser;
  logic init_awvalid;
  logic init_awready;
  logic [DataWidth-1:0] init_wdata;
  logic [StrobeWidth-1:0] init_wstrb;
  logic [WUserWidth-1:0] init_wuser;
  logic init_wvalid;
  logic init_wready;
  logic [AxiRespWidth-1:0] init_bresp;
  logic [BUserWidth-1:0] init_buser;
  logic init_bvalid;
  logic init_bready;
  logic [AddrWidth-1:0] init_araddr;
  logic [AxiProtWidth-1:0] init_arprot;
  logic [ARUserWidth-1:0] init_aruser;
  logic init_arvalid;
  logic init_arready;
  logic [DataWidth-1:0] init_rdata;
  logic [AxiRespWidth-1:0] init_rresp;
  logic [RUserWidth-1:0] init_ruser;
  logic init_rvalid;
  logic init_rready;

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  br_amba_axil_timing_slice #(
      .AddrWidth  (AddrWidth),
      .DataWidth  (DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth (WUserWidth),
      .ARUserWidth(ARUserWidth),
      .RUserWidth (RUserWidth),
      .BUserWidth (BUserWidth)
  ) dut (
      .clk,
      .rst,
      .target_awaddr,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wvalid,
      .target_wready,
      .target_bresp,
      .target_buser,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rdata,
      .target_rresp,
      .target_ruser,
      .target_rvalid,
      .target_rready,
      .init_awaddr,
      .init_awprot,
      .init_awuser,
      .init_awvalid,
      .init_awready,
      .init_wdata,
      .init_wstrb,
      .init_wuser,
      .init_wvalid,
      .init_wready,
      .init_bresp,
      .init_buser,
      .init_bvalid,
      .init_bready,
      .init_araddr,
      .init_arprot,
      .init_aruser,
      .init_arvalid,
      .init_arready,
      .init_rdata,
      .init_rresp,
      .init_ruser,
      .init_rvalid,
      .init_rready
  );

  br_amba_axil_timing_slice_driver #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axil_driver (
      .clk,
      .rst,
      .target_awaddr,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wvalid,
      .target_wready,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rvalid,
      .target_rready,
      .init_awvalid,
      .init_awready,
      .init_wvalid,
      .init_wready,
      .init_bresp,
      .init_buser,
      .init_bvalid,
      .init_bready,
      .init_arvalid,
      .init_arready,
      .init_rdata,
      .init_rresp,
      .init_ruser,
      .init_rvalid,
      .init_rready,
      .failed(driver_failed)
  );

  br_amba_axil_timing_slice_monitor #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axil_monitor (
      .clk,
      .rst,
      .target_awaddr,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wvalid,
      .target_wready,
      .target_bresp,
      .target_buser,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rdata,
      .target_rresp,
      .target_ruser,
      .target_rvalid,
      .target_rready,
      .init_awaddr,
      .init_awprot,
      .init_awuser,
      .init_awvalid,
      .init_awready,
      .init_wdata,
      .init_wstrb,
      .init_wuser,
      .init_wvalid,
      .init_wready,
      .init_bresp,
      .init_buser,
      .init_bvalid,
      .init_bready,
      .init_araddr,
      .init_arprot,
      .init_aruser,
      .init_arvalid,
      .init_arready,
      .init_rdata,
      .init_rresp,
      .init_ruser,
      .init_rvalid,
      .init_rready,
      .failed(monitor_failed)
  );

  function automatic logic [255:0] payload_pattern(input int index, input int salt);
    for (int word = 0; word < 8; word++) begin
      payload_pattern[word*32+:32] = 32'((index + 1) * (salt + (word * 19)) ^
                                         (PayloadSeed >> (word % 7)) ^
                                         (32'h2040_8102 << (word % 5)));
    end
  endfunction

  function automatic axil_aw_t get_aw_input(input int index);
    logic [255:0] payload;
    payload = payload_pattern(index, 11);
    get_aw_input.addr = payload[AddrWidth-1:0];
    get_aw_input.prot = payload[64+:AxiProtWidth];
    get_aw_input.user = payload[96+:AWUserWidth];
  endfunction

  function automatic axil_w_t get_w_input(input int index);
    logic [255:0] payload;
    payload = payload_pattern(index, 23);
    get_w_input.data = payload[DataWidth-1:0];
    get_w_input.strb = StrobeWidth'(payload[128+:StrobeWidth]) | StrobeWidth'(1'b1);
    get_w_input.user = payload[160+:WUserWidth];
  endfunction

  function automatic axil_ar_t get_ar_input(input int index);
    logic [255:0] payload;
    payload = payload_pattern(index, 37);
    get_ar_input.addr = payload[AddrWidth-1:0];
    get_ar_input.prot = payload[64+:AxiProtWidth];
    get_ar_input.user = payload[96+:ARUserWidth];
  endfunction

  function automatic axil_b_t get_b_input(input int index);
    logic [255:0] payload;
    payload = payload_pattern(index, 47);
    get_b_input.resp = AxiRespWidth'(index);
    get_b_input.user = payload[32+:BUserWidth];
  endfunction

  function automatic axil_r_t get_r_input(input int index);
    logic [255:0] payload;
    payload = payload_pattern(index, 59);
    get_r_input.data = payload[DataWidth-1:0];
    get_r_input.resp = AxiRespWidth'(index + 1);
    get_r_input.user = payload[160+:RUserWidth];
  endfunction

  task automatic run_timing_slice_test(input axil_timing_slice_controls_t controls);
    axil_aw_t aw_input;
    axil_w_t  w_input;
    axil_ar_t ar_input;
    axil_b_t  b_input;
    axil_r_t  r_input;

    aw_input = get_aw_input(0);
    w_input  = get_w_input(0);
    ar_input = get_ar_input(0);
    b_input  = get_b_input(0);
    r_input  = get_r_input(0);

    axil_driver.init_idle();
    axil_monitor.init_idle();
    td.reset_dut();
    td.wait_cycles();

    td.check(!init_awvalid, "init_awvalid asserted after reset");
    td.check(!init_wvalid, "init_wvalid asserted after reset");
    td.check(!target_bvalid, "target_bvalid asserted after reset");
    td.check(!init_arvalid, "init_arvalid asserted after reset");
    td.check(!target_rvalid, "target_rvalid asserted after reset");

    fork
      axil_driver.run(controls.num_writes, controls.num_reads, controls.valid_gap_cycles,
                      controls.max_stall_cycles, aw_input, w_input, ar_input, b_input, r_input);
      axil_monitor.run(controls.num_writes, controls.num_reads);
    join
  endtask

  task automatic check_timing_slice_status(input string scenario);
    td.check(!driver_failed, $sformatf(
             "%s: AXI-Lite timing-slice driver reported one or more failures", scenario));
    td.check(!monitor_failed, $sformatf(
             "%s: AXI-Lite timing-slice monitor reported one or more failures", scenario));
  endtask

  task automatic test_directed_backpressure();
    axil_timing_slice_controls_t controls;

    controls = '{default: 0};
    controls.num_writes = 1;
    controls.num_reads = 1;
    controls.valid_gap_cycles = DirectedValidGapCycles;
    controls.max_stall_cycles = DirectedStallCycles;
    run_timing_slice_test(controls);
    check_timing_slice_status("directed backpressure");
  endtask

  task automatic test_multi_transaction_ordering();
    axil_timing_slice_controls_t controls;

    controls = '{default: 0};
    controls.num_writes = NumTransactions;
    controls.num_reads = NumTransactions;
    controls.valid_gap_cycles = RandomizedValidGapCycles;
    controls.max_stall_cycles = RandomizedStallCycles;
    run_timing_slice_test(controls);
    check_timing_slice_status("multi-transaction ordering");
  endtask

  initial begin
    axil_driver.init_idle();
    axil_monitor.init_idle();

    test_directed_backpressure();
    test_multi_transaction_ordering();

    td.check(!driver_failed, "AXI-Lite timing-slice driver reported one or more failures");
    td.check(!monitor_failed, "AXI-Lite timing-slice monitor reported one or more failures");
    td.finish();
  end

endmodule : br_amba_axil_timing_slice_tb
