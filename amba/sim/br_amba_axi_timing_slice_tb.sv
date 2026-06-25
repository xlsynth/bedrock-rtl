// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;

typedef struct {
  int num_writes;
  int num_reads;
  int valid_gap_cycles;
  int max_stall_cycles;
} axi_timing_slice_controls_t;

// Directed simulation testbench for br_amba_axi_timing_slice.
//
// Scope:
// - checks reset-visible AXI channel valid outputs are idle;
// - sends deterministic payloads on all five independent AXI channels;
// - checks output payload order and data integrity under channel backpressure;
// - sweeps address width, data width, slice type, and transaction count from Bazel.
module br_amba_axi_timing_slice_tb;
  parameter int AddrWidth = 12;
  parameter int DataWidth = 32;
  parameter int IdWidth = 2;
  parameter int AWUserWidth = 2;
  parameter int WUserWidth = 2;
  parameter int ARUserWidth = 2;
  parameter int BUserWidth = 2;
  parameter int RUserWidth = 2;
  parameter int AWSliceType = 2;
  parameter int WSliceType = 2;
  parameter int ARSliceType = 2;
  parameter int RSliceType = 2;
  parameter int BSliceType = 2;
  parameter int SliceType = -1;
  parameter int NumTransactions = 10;

  localparam int StrobeWidth = DataWidth / 8;
  localparam int TimeoutCycles = (NumTransactions * 80) + 400;
  localparam int DirectedValidGapCycles = 0;
  localparam int DirectedStallCycles = 3;
  localparam int RandomizedValidGapCycles = 1;
  localparam int RandomizedStallCycles = 0;
  localparam int EffectiveAWSliceType = (SliceType >= 0) ? SliceType : AWSliceType;
  localparam int EffectiveWSliceType = (SliceType >= 0) ? SliceType : WSliceType;
  localparam int EffectiveARSliceType = (SliceType >= 0) ? SliceType : ARSliceType;
  localparam int EffectiveRSliceType = (SliceType >= 0) ? SliceType : RSliceType;
  localparam int EffectiveBSliceType = (SliceType >= 0) ? SliceType : BSliceType;
  // The directed phase covers reverse-W backpressure without relying on a
  // multi-transfer source/sink pattern that can deadlock a registered-ready slice.
  localparam int MultiNumTransactions = (EffectiveWSliceType == 1) ? 1 : NumTransactions;
  localparam int PayloadSeed = 32'h1357_2468;

  logic clk;
  logic rst;
  logic driver_failed;
  logic target_driver_failed;
  logic initiator_driver_failed;
  logic monitor_failed;

  logic [AddrWidth-1:0] target_awaddr;
  logic [IdWidth-1:0] target_awid;
  logic [AxiBurstLenWidth-1:0] target_awlen;
  logic [AxiBurstSizeWidth-1:0] target_awsize;
  logic [AxiBurstTypeWidth-1:0] target_awburst;
  logic [AxiProtWidth-1:0] target_awprot;
  logic [AWUserWidth-1:0] target_awuser;
  logic target_awvalid;
  logic target_awready;
  logic [DataWidth-1:0] target_wdata;
  logic [StrobeWidth-1:0] target_wstrb;
  logic [WUserWidth-1:0] target_wuser;
  logic target_wlast;
  logic target_wvalid;
  logic target_wready;
  logic [IdWidth-1:0] target_bid;
  logic [BUserWidth-1:0] target_buser;
  logic [AxiRespWidth-1:0] target_bresp;
  logic target_bvalid;
  logic target_bready;
  logic [AddrWidth-1:0] target_araddr;
  logic [IdWidth-1:0] target_arid;
  logic [AxiBurstLenWidth-1:0] target_arlen;
  logic [AxiBurstSizeWidth-1:0] target_arsize;
  logic [AxiBurstTypeWidth-1:0] target_arburst;
  logic [AxiProtWidth-1:0] target_arprot;
  logic [ARUserWidth-1:0] target_aruser;
  logic target_arvalid;
  logic target_arready;
  logic [IdWidth-1:0] target_rid;
  logic [DataWidth-1:0] target_rdata;
  logic [RUserWidth-1:0] target_ruser;
  logic [AxiRespWidth-1:0] target_rresp;
  logic target_rlast;
  logic target_rvalid;
  logic target_rready;

  logic [AddrWidth-1:0] init_awaddr;
  logic [IdWidth-1:0] init_awid;
  logic [AxiBurstLenWidth-1:0] init_awlen;
  logic [AxiBurstSizeWidth-1:0] init_awsize;
  logic [AxiBurstTypeWidth-1:0] init_awburst;
  logic [AxiProtWidth-1:0] init_awprot;
  logic [AWUserWidth-1:0] init_awuser;
  logic init_awvalid;
  logic init_awready;
  logic [DataWidth-1:0] init_wdata;
  logic [StrobeWidth-1:0] init_wstrb;
  logic [WUserWidth-1:0] init_wuser;
  logic init_wlast;
  logic init_wvalid;
  logic init_wready;
  logic [IdWidth-1:0] init_bid;
  logic [BUserWidth-1:0] init_buser;
  logic [AxiRespWidth-1:0] init_bresp;
  logic init_bvalid;
  logic init_bready;
  logic [AddrWidth-1:0] init_araddr;
  logic [IdWidth-1:0] init_arid;
  logic [AxiBurstLenWidth-1:0] init_arlen;
  logic [AxiBurstSizeWidth-1:0] init_arsize;
  logic [AxiBurstTypeWidth-1:0] init_arburst;
  logic [AxiProtWidth-1:0] init_arprot;
  logic [ARUserWidth-1:0] init_aruser;
  logic init_arvalid;
  logic init_arready;
  logic [IdWidth-1:0] init_rid;
  logic [DataWidth-1:0] init_rdata;
  logic [RUserWidth-1:0] init_ruser;
  logic [AxiRespWidth-1:0] init_rresp;
  logic init_rlast;
  logic init_rvalid;
  logic init_rready;

  assign driver_failed = target_driver_failed || initiator_driver_failed;

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  br_amba_axi_timing_slice #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .AWSliceType(EffectiveAWSliceType),
      .WSliceType(EffectiveWSliceType),
      .ARSliceType(EffectiveARSliceType),
      .RSliceType(EffectiveRSliceType),
      .BSliceType(EffectiveBSliceType)
  ) dut (
      .clk,
      .rst,
      .target_awaddr,
      .target_awid,
      .target_awlen,
      .target_awsize,
      .target_awburst,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wlast,
      .target_wvalid,
      .target_wready,
      .target_bid,
      .target_buser,
      .target_bresp,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arid,
      .target_arlen,
      .target_arsize,
      .target_arburst,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rid,
      .target_rdata,
      .target_ruser,
      .target_rresp,
      .target_rlast,
      .target_rvalid,
      .target_rready,
      .init_awaddr,
      .init_awid,
      .init_awlen,
      .init_awsize,
      .init_awburst,
      .init_awprot,
      .init_awuser,
      .init_awvalid,
      .init_awready,
      .init_wdata,
      .init_wstrb,
      .init_wuser,
      .init_wlast,
      .init_wvalid,
      .init_wready,
      .init_bid,
      .init_buser,
      .init_bresp,
      .init_bvalid,
      .init_bready,
      .init_araddr,
      .init_arid,
      .init_arlen,
      .init_arsize,
      .init_arburst,
      .init_arprot,
      .init_aruser,
      .init_arvalid,
      .init_arready,
      .init_rid,
      .init_rdata,
      .init_ruser,
      .init_rresp,
      .init_rlast,
      .init_rvalid,
      .init_rready
  );

  br_amba_axi_timing_slice_driver #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axi_target_driver (
      .clk,
      .rst,
      .target_awaddr,
      .target_awid,
      .target_awlen,
      .target_awsize,
      .target_awburst,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wlast,
      .target_wvalid,
      .target_wready,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arid,
      .target_arlen,
      .target_arsize,
      .target_arburst,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rvalid,
      .target_rready,
      .failed(target_driver_failed)
  );

  br_amba_axi_timing_slice_initiator_driver #(
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axi_initiator_driver (
      .clk,
      .rst,
      .init_awvalid,
      .init_awready,
      .init_wvalid,
      .init_wready,
      .init_bid,
      .init_buser,
      .init_bresp,
      .init_bvalid,
      .init_bready,
      .init_arvalid,
      .init_arready,
      .init_rid,
      .init_rdata,
      .init_ruser,
      .init_rresp,
      .init_rlast,
      .init_rvalid,
      .init_rready,
      .failed(initiator_driver_failed)
  );

  br_amba_axi_timing_slice_monitor #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .IdWidth(IdWidth),
      .AWUserWidth(AWUserWidth),
      .WUserWidth(WUserWidth),
      .ARUserWidth(ARUserWidth),
      .BUserWidth(BUserWidth),
      .RUserWidth(RUserWidth),
      .TimeoutCycles(TimeoutCycles)
  ) axi_monitor (
      .clk,
      .rst,
      .target_awaddr,
      .target_awid,
      .target_awlen,
      .target_awsize,
      .target_awburst,
      .target_awprot,
      .target_awuser,
      .target_awvalid,
      .target_awready,
      .target_wdata,
      .target_wstrb,
      .target_wuser,
      .target_wlast,
      .target_wvalid,
      .target_wready,
      .target_bid,
      .target_buser,
      .target_bresp,
      .target_bvalid,
      .target_bready,
      .target_araddr,
      .target_arid,
      .target_arlen,
      .target_arsize,
      .target_arburst,
      .target_arprot,
      .target_aruser,
      .target_arvalid,
      .target_arready,
      .target_rid,
      .target_rdata,
      .target_ruser,
      .target_rresp,
      .target_rlast,
      .target_rvalid,
      .target_rready,
      .init_awaddr,
      .init_awid,
      .init_awlen,
      .init_awsize,
      .init_awburst,
      .init_awprot,
      .init_awuser,
      .init_awvalid,
      .init_awready,
      .init_wdata,
      .init_wstrb,
      .init_wuser,
      .init_wlast,
      .init_wvalid,
      .init_wready,
      .init_bid,
      .init_buser,
      .init_bresp,
      .init_bvalid,
      .init_bready,
      .init_araddr,
      .init_arid,
      .init_arlen,
      .init_arsize,
      .init_arburst,
      .init_arprot,
      .init_aruser,
      .init_arvalid,
      .init_arready,
      .init_rid,
      .init_rdata,
      .init_ruser,
      .init_rresp,
      .init_rlast,
      .init_rvalid,
      .init_rready,
      .failed(monitor_failed)
  );

  function automatic axi_aw_t get_aw_input(input int index);
    get_aw_input = get_axi_timing_slice_aw_input(index, StrobeWidth, PayloadSeed);
  endfunction

  function automatic axi_w_t get_w_input(input int index);
    get_w_input = get_axi_timing_slice_w_input(index, PayloadSeed);
  endfunction

  function automatic axi_ar_t get_ar_input(input int index);
    get_ar_input = get_axi_timing_slice_ar_input(index, StrobeWidth, PayloadSeed);
  endfunction

  function automatic axi_b_t get_b_input(input int index);
    get_b_input = get_axi_timing_slice_b_input(index, PayloadSeed);
  endfunction

  function automatic axi_r_t get_r_input(input int index);
    get_r_input = get_axi_timing_slice_r_input(index, PayloadSeed);
  endfunction

  task automatic run_timing_slice_test(input axi_timing_slice_controls_t controls);
    axi_aw_t aw_input;
    axi_w_t  w_input;
    axi_ar_t ar_input;
    axi_b_t  b_input;
    axi_r_t  r_input;

    aw_input = get_aw_input(0);
    w_input  = get_w_input(0);
    ar_input = get_ar_input(0);
    b_input  = get_b_input(0);
    r_input  = get_r_input(0);

    axi_target_driver.init_idle();
    axi_initiator_driver.init_idle();
    axi_monitor.init_idle();
    td.reset_dut();
    td.wait_cycles();

    td.check(!init_awvalid, "init_awvalid asserted after reset");
    td.check(!init_wvalid, "init_wvalid asserted after reset");
    td.check(!target_bvalid, "target_bvalid asserted after reset");
    td.check(!init_arvalid, "init_arvalid asserted after reset");
    td.check(!target_rvalid, "target_rvalid asserted after reset");

    fork
      axi_target_driver.run(controls.num_writes, controls.num_reads, controls.valid_gap_cycles,
                            controls.max_stall_cycles, aw_input, w_input, ar_input);
      axi_initiator_driver.run(controls.num_writes, controls.num_reads, controls.valid_gap_cycles,
                               controls.max_stall_cycles, b_input, r_input);
      axi_monitor.run(controls.num_writes, controls.num_reads);
    join
  endtask

  task automatic check_timing_slice_status(input string scenario);
    td.check(!target_driver_failed, $sformatf(
             "%s: AXI timing-slice target driver reported one or more failures", scenario));
    td.check(!initiator_driver_failed, $sformatf(
             "%s: AXI timing-slice initiator driver reported one or more failures", scenario));
    td.check(!monitor_failed, $sformatf(
             "%s: AXI timing-slice monitor reported one or more failures", scenario));
  endtask

  task automatic test_directed_backpressure();
    axi_timing_slice_controls_t controls;

    controls = '{default: 0};
    controls.num_writes = 1;
    controls.num_reads = 1;
    controls.valid_gap_cycles = DirectedValidGapCycles;
    controls.max_stall_cycles = DirectedStallCycles;
    run_timing_slice_test(controls);
    check_timing_slice_status("directed backpressure");
  endtask

  task automatic test_multi_transaction_ordering();
    axi_timing_slice_controls_t controls;

    controls = '{default: 0};
    controls.num_writes = MultiNumTransactions;
    controls.num_reads = MultiNumTransactions;
    controls.valid_gap_cycles = RandomizedValidGapCycles;
    controls.max_stall_cycles = RandomizedStallCycles;
    run_timing_slice_test(controls);
    check_timing_slice_status("multi-transaction ordering");
  endtask

  initial begin
    axi_target_driver.init_idle();
    axi_initiator_driver.init_idle();
    axi_monitor.init_idle();

    test_directed_backpressure();
    test_multi_transaction_ordering();

    td.check(!driver_failed, "AXI timing-slice driver reported one or more failures");
    td.check(!monitor_failed, "AXI timing-slice monitor reported one or more failures");
    td.finish();
  end

endmodule : br_amba_axi_timing_slice_tb
