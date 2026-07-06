// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_sim_pkg::*;

typedef enum int {
  AxiDefaultResponseKindOkay   = 0,
  AxiDefaultResponseKindSlverr = 1,
  AxiDefaultResponseKindDecerr = 2
} axi_default_response_kind_e;

typedef struct {
  int awvalid;
  int wvalid;
  int arvalid;
} axi_default_delays_t;

// Directed simulation testbench for br_amba_axi_default_target.
//
// Scope:
// - checks reset-visible AXI response outputs are idle;
// - verifies write responses when address and data channels arrive with skew;
// - checks read response ID, response code, data, and last-beat behavior under backpressure;
// - sweeps data width, response-code mode, transaction count, and single-/multi-beat mode.
module br_amba_axi_default_target_tb;
  parameter int DataWidth = 32;
  parameter int NumTransactions = 1;
  parameter int AxiIdWidth = 2;
  parameter bit SingleBeat = 0;
  parameter axi_default_response_kind_e ResponseKind = AxiDefaultResponseKindDecerr;

  localparam int TimeoutCycles = (NumTransactions * 80) + 200;
  localparam int ChannelSkewCycles = 3;
  localparam int MaxReadyStallCycles = 9;
  localparam int MaxReadLen = 3;
  localparam logic [63:0] DefaultReadDataFull = 64'hc001_d00d_f00d_5eed;
  localparam logic [DataWidth-1:0] DefaultReadData = DefaultReadDataFull[DataWidth-1:0];
  localparam logic [AxiRespWidth-1:0] ExpectedResp =
      ResponseKind == AxiDefaultResponseKindDecerr ? AxiRespDecerr :
      ResponseKind == AxiDefaultResponseKindSlverr ? AxiRespSlverr : AxiRespOkay;
  localparam bit DecodeError = ResponseKind == AxiDefaultResponseKindDecerr;
  localparam bit SlvErr = ResponseKind == AxiDefaultResponseKindSlverr;
  localparam int AxiLenWidth = SingleBeat ? 1 : AxiBurstLenWidth;

  logic clk;
  logic rst;

  logic target_awvalid;
  logic target_awready;
  logic [AxiIdWidth-1:0] target_awid;
  logic [AxiLenWidth-1:0] target_awlen;
  logic target_wvalid;
  logic target_wready;
  logic target_wlast;
  logic target_bvalid;
  logic target_bready;
  logic [AxiIdWidth-1:0] target_bid;
  logic [AxiRespWidth-1:0] target_bresp;
  logic target_arvalid;
  logic target_arready;
  logic [AxiIdWidth-1:0] target_arid;
  logic [AxiLenWidth-1:0] target_arlen;
  logic target_rvalid;
  logic target_rready;
  logic [DataWidth-1:0] target_rdata;
  logic [AxiRespWidth-1:0] target_rresp;
  logic [AxiIdWidth-1:0] target_rid;
  logic target_rlast;
  logic driver_failed;
  logic monitor_failed;
  logic [br_amba_axi_sim_pkg::AxiAddrWidth-1:0] unused_awaddr;
  logic [br_amba_axi_sim_pkg::AxiIdWidth-1:0] driver_awid;
  logic [AxiBurstLenWidth-1:0] full_awlen;
  logic [AxiBurstSizeWidth-1:0] unused_awsize;
  logic [AxiBurstTypeWidth-1:0] unused_awburst;
  logic [AxiProtWidth-1:0] unused_awprot;
  logic [br_amba_axi_sim_pkg::AxiUserWidth-1:0] unused_awuser;
  logic [br_amba_axi_sim_pkg::AxiDataWidth-1:0] unused_wdata;
  logic [br_amba_axi_sim_pkg::AxiStrobeWidth-1:0] unused_wstrb;
  logic [br_amba_axi_sim_pkg::AxiUserWidth-1:0] unused_wuser;
  logic [br_amba_axi_sim_pkg::AxiAddrWidth-1:0] unused_araddr;
  logic [br_amba_axi_sim_pkg::AxiIdWidth-1:0] driver_arid;
  logic [AxiBurstLenWidth-1:0] full_arlen;
  logic [AxiBurstSizeWidth-1:0] unused_arsize;
  logic [AxiBurstTypeWidth-1:0] unused_arburst;
  logic [AxiProtWidth-1:0] unused_arprot;
  logic [br_amba_axi_sim_pkg::AxiUserWidth-1:0] unused_aruser;

  assign target_awid  = AxiIdWidth'(driver_awid);
  assign target_awlen = AxiLenWidth'(full_awlen);
  assign target_arid  = AxiIdWidth'(driver_arid);
  assign target_arlen = AxiLenWidth'(full_arlen);

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  br_amba_axi_default_target #(
      .DataWidth(DataWidth),
      .DecodeError(DecodeError),
      .SlvErr(SlvErr),
      .AxiIdWidth(AxiIdWidth),
      .SingleBeat(SingleBeat),
      .DefaultReadData(DefaultReadData)
  ) dut (
      .clk,
      .rst,
      .target_awvalid,
      .target_awready,
      .target_awid,
      .target_awlen,
      .target_wvalid,
      .target_wready,
      .target_wlast,
      .target_bvalid,
      .target_bready,
      .target_bid,
      .target_bresp,
      .target_arvalid,
      .target_arready,
      .target_arid,
      .target_arlen,
      .target_rvalid,
      .target_rready,
      .target_rdata,
      .target_rresp,
      .target_rid,
      .target_rlast
  );

  br_amba_axi_target_driver #(
      .TimeoutCycles(TimeoutCycles)
  ) axi_driver (
      .clk,
      .rst,
      .target_awaddr(unused_awaddr),
      .target_awvalid,
      .target_awready,
      .target_awid(driver_awid),
      .target_awlen(full_awlen),
      .target_awsize(unused_awsize),
      .target_awburst(unused_awburst),
      .target_awprot(unused_awprot),
      .target_awuser(unused_awuser),
      .target_wdata(unused_wdata),
      .target_wstrb(unused_wstrb),
      .target_wuser(unused_wuser),
      .target_wvalid,
      .target_wready,
      .target_wlast,
      .target_bvalid,
      .target_bready,
      .target_araddr(unused_araddr),
      .target_arvalid,
      .target_arready,
      .target_arid(driver_arid),
      .target_arlen(full_arlen),
      .target_arsize(unused_arsize),
      .target_arburst(unused_arburst),
      .target_arprot(unused_arprot),
      .target_aruser(unused_aruser),
      .target_rvalid,
      .target_rready,
      .failed(driver_failed)
  );

  br_amba_axi_default_target_monitor #(
      .DataWidth(DataWidth),
      .AxiIdWidth(AxiIdWidth),
      .SingleBeat(SingleBeat),
      .ExpectedResp(ExpectedResp),
      .DefaultReadData(DefaultReadData),
      .TimeoutCycles(TimeoutCycles)
  ) axi_monitor (
      .clk,
      .rst,
      .target_awvalid,
      .target_awready,
      .target_awid,
      .target_awlen,
      .target_wvalid,
      .target_wready,
      .target_wlast,
      .target_bid,
      .target_bresp,
      .target_bvalid,
      .target_bready,
      .target_arvalid,
      .target_arready,
      .target_arid,
      .target_arlen,
      .target_rdata,
      .target_rresp,
      .target_rid,
      .target_rlast,
      .target_rvalid,
      .target_rready,
      .failed(monitor_failed)
  );

  function automatic axi_aw_t get_aw_input(input int index);
    get_aw_input = '0;
    get_aw_input.addr = AxiAddrWidth'($urandom());
    get_aw_input.id = br_amba_axi_sim_pkg::AxiIdWidth'(AxiIdWidth'($urandom()));
    get_aw_input.len = get_axi_default_target_aw_len(index, SingleBeat, MaxReadLen);
    get_aw_input.size = AxiBurstSizeWidth'($clog2(br_amba_axi_sim_pkg::AxiStrobeWidth));
    get_aw_input.burst = AxiBurstIncr;
    get_aw_input.prot = AxiProtWidth'($urandom());
    get_aw_input.user = AxiUserWidth'($urandom());
  endfunction

  function automatic axi_w_t get_w_input();
    get_w_input = '0;
    for (int word = 0; word < br_amba_axi_sim_pkg::AxiDataWidth / 32; word++) begin
      get_w_input.data[word*32+:32] = $urandom();
    end
    get_w_input.strb = AxiStrobeWidth'($urandom()) | AxiStrobeWidth'(1'b1);
    get_w_input.user = AxiUserWidth'($urandom());
    get_w_input.last = 1'b1;
  endfunction

  function automatic axi_ar_t get_ar_input(input int index);
    get_ar_input = '0;
    get_ar_input.addr = AxiAddrWidth'($urandom());
    get_ar_input.id = br_amba_axi_sim_pkg::AxiIdWidth'(AxiIdWidth'($urandom()));
    get_ar_input.len = get_axi_default_target_ar_len(index, SingleBeat, MaxReadLen);
    get_ar_input.size = AxiBurstSizeWidth'($clog2(br_amba_axi_sim_pkg::AxiStrobeWidth));
    get_ar_input.burst = AxiBurstIncr;
    get_ar_input.prot = AxiProtWidth'($urandom());
    get_ar_input.user = AxiUserWidth'($urandom());
  endfunction

  task automatic test_write_address_before_data();
    axi_default_delays_t delays;
    axi_aw_t aw_input;
    axi_w_t w_input;

    delays = '{default: 0};
    delays.wvalid = ChannelSkewCycles;
    aw_input = get_aw_input(0);
    w_input = get_w_input();
    fork
      axi_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid),
                     .max_stall_cycles(MaxReadyStallCycles), .awaddr(aw_input.addr),
                     .awid(aw_input.id), .awlen(aw_input.len), .awsize(aw_input.size),
                     .awburst(aw_input.burst), .awprot(aw_input.prot), .awuser(aw_input.user),
                     .wdata(w_input.data), .wstrb(w_input.strb), .wuser(w_input.user),
                     .wlast(w_input.last), .vary_burst_len(!SingleBeat), .vary_wlast(1'b0));
      axi_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_write_data_before_address();
    axi_default_delays_t delays;
    axi_aw_t aw_input;
    axi_w_t w_input;

    delays = '{default: 0};
    delays.awvalid = ChannelSkewCycles;
    aw_input = get_aw_input(0);
    w_input = get_w_input();
    fork
      axi_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid),
                     .max_stall_cycles(MaxReadyStallCycles), .awaddr(aw_input.addr),
                     .awid(aw_input.id), .awlen(aw_input.len), .awsize(aw_input.size),
                     .awburst(aw_input.burst), .awprot(aw_input.prot), .awuser(aw_input.user),
                     .wdata(w_input.data), .wstrb(w_input.strb), .wuser(w_input.user),
                     .wlast(w_input.last), .vary_burst_len(!SingleBeat), .vary_wlast(1'b0));
      axi_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_read_backpressure();
    axi_default_delays_t delays;
    axi_ar_t ar_input;

    delays   = '{default: 0};
    ar_input = get_ar_input(0);
    fork
      axi_driver.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid),
                     .max_stall_cycles(MaxReadyStallCycles), .araddr(ar_input.addr),
                     .arid(ar_input.id), .arlen(ar_input.len), .arsize(ar_input.size),
                     .arburst(ar_input.burst), .arprot(ar_input.prot), .aruser(ar_input.user),
                     .accept_r_burst_len(1'b1), .vary_burst_len(!SingleBeat));
      axi_monitor.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid));
    join
  endtask

  initial begin
    axi_driver.init_idle();
    axi_monitor.init_idle();
    td.reset_dut();
    td.wait_cycles();

    td.check(!target_bvalid, "B valid asserted after reset");
    td.check(!target_rvalid, "R valid asserted after reset");

    test_write_address_before_data();
    test_write_data_before_address();
    test_read_backpressure();

    td.check(!driver_failed, "AXI driver reported one or more failures");
    td.check(!monitor_failed, "AXI monitor reported one or more failures");
    td.finish();
  end

endmodule : br_amba_axi_default_target_tb
