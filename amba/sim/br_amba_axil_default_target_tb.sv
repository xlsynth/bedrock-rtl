// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_sim_pkg::*;

typedef enum int {
  ResponseKindOkay   = 0,
  ResponseKindSlverr = 1,
  ResponseKindDecerr = 2
} response_kind_e;

typedef struct {
  int awvalid;
  int wvalid;
  int arvalid;
} axil_delays_t;

// Directed simulation testbench for br_amba_axil_default_target.
//
// Scope:
// - checks reset-visible AXI-Lite response outputs are idle;
// - verifies write responses when address and data channels arrive with skew;
// - checks read response code and default read data under response-channel backpressure;
// - sweeps data width, response-code mode, and transaction count from Bazel.
module br_amba_axil_default_target_tb;
  parameter int DataWidth = 32;
  parameter int NumTransactions = 1;
  parameter response_kind_e ResponseKind = ResponseKindDecerr;

  localparam int TimeoutCycles = 20;
  localparam int ChannelSkewCycles = 3;
  localparam logic [63:0] DefaultReadDataFull = 64'hf00d_cafe_1234_5678;
  localparam logic [DataWidth-1:0] DefaultReadData = DefaultReadDataFull[DataWidth-1:0];
  localparam logic [AxiRespWidth-1:0] ExpectedResp =
      ResponseKind == ResponseKindDecerr ? AxiRespDecerr :
      ResponseKind == ResponseKindSlverr ? AxiRespSlverr : AxiRespOkay;
  localparam bit DecodeError = ResponseKind == ResponseKindDecerr;
  localparam bit SlvErr = ResponseKind == ResponseKindSlverr;

  logic clk;
  logic rst;

  logic target_awvalid;
  logic target_awready;
  logic target_wvalid;
  logic target_wready;
  logic [AxiRespWidth-1:0] target_bresp;
  logic target_bvalid;
  logic target_bready;
  logic target_arvalid;
  logic target_arready;
  logic [DataWidth-1:0] target_rdata;
  logic [AxiRespWidth-1:0] target_rresp;
  logic target_rvalid;
  logic target_rready;
  logic driver_failed;
  logic monitor_failed;
  logic timeout_failed;
  event timeout_tick;

  always @(posedge clk) begin
    ->timeout_tick;
  end

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  br_amba_axil_default_target #(
      .DataWidth(DataWidth),
      .DecodeError(DecodeError),
      .SlvErr(SlvErr),
      .DefaultReadData(DefaultReadData)
  ) dut (
      .clk,
      .rst,
      .target_awvalid,
      .target_awready,
      .target_wvalid,
      .target_wready,
      .target_bresp,
      .target_bvalid,
      .target_bready,
      .target_arvalid,
      .target_arready,
      .target_rdata,
      .target_rresp,
      .target_rvalid,
      .target_rready
  );

  br_amba_axil_completer_driver #(
      .TimeoutCycles(TimeoutCycles)
  ) axil_driver (
      .clk,
      .rst,
      .target_awvalid,
      .target_awready,
      .target_wvalid,
      .target_wready,
      .target_bvalid,
      .target_bready,
      .target_arvalid,
      .target_arready,
      .target_rvalid,
      .target_rready,
      .failed(driver_failed)
  );

  br_amba_axil_monitor #(
      .DataWidth(DataWidth)
  ) axil_monitor (
      .clk(clk),
      .rst(rst),
      .axil_awaddr('0),
      .axil_awprot('0),
      .axil_awuser('0),
      .axil_awvalid(target_awvalid),
      .axil_awready(target_awready),
      .axil_wdata('0),
      .axil_wstrb('0),
      .axil_wuser('0),
      .axil_wvalid(target_wvalid),
      .axil_wready(target_wready),
      .axil_bresp(target_bresp),
      .axil_buser('0),
      .axil_bvalid(target_bvalid),
      .axil_bready(target_bready),
      .axil_araddr('0),
      .axil_arprot('0),
      .axil_aruser('0),
      .axil_arvalid(target_arvalid),
      .axil_arready(target_arready),
      .axil_rdata(target_rdata),
      .axil_rresp(target_rresp),
      .axil_ruser('0),
      .axil_rvalid(target_rvalid),
      .axil_rready(target_rready),
      .failed(monitor_failed)
  );

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  // TODO: Move these DUT-specific checking tasks into a default-target scoreboard.
  task automatic wait_for_aw_handshake();
    logic observed = 1'b0;

    fork
      begin
        wait (target_awvalid && target_awready);
        observed = 1'b1;
      end
      timeout(timeout_tick, TimeoutCycles, "Timeout waiting for AXI-Lite AW handshake",
              timeout_failed);
    join_any
    disable fork;
    td.check(observed, "AXI-Lite AW handshake was not observed");
  endtask

  task automatic wait_for_w_handshake();
    logic observed = 1'b0;

    fork
      begin
        wait (target_wvalid && target_wready);
        observed = 1'b1;
      end
      timeout(timeout_tick, TimeoutCycles, "Timeout waiting for AXI-Lite W handshake",
              timeout_failed);
    join_any
    disable fork;
    td.check(observed, "AXI-Lite W handshake was not observed");
  endtask

  task automatic wait_for_b_handshake();
    logic observed = 1'b0;

    fork
      begin
        @(posedge clk);
        while (!(target_bvalid && target_bready)) @(posedge clk);
        observed = 1'b1;
      end
      timeout(timeout_tick, TimeoutCycles, "Timeout waiting for AXI-Lite B handshake",
              timeout_failed);
    join_any
    disable fork;
    td.check(observed, "AXI-Lite B handshake was not observed");
  endtask

  task automatic wait_for_r_handshake();
    logic observed = 1'b0;

    fork
      begin
        @(posedge clk);
        while (!(target_rvalid && target_rready)) @(posedge clk);
        observed = 1'b1;
      end
      timeout(timeout_tick, TimeoutCycles, "Timeout waiting for AXI-Lite R handshake",
              timeout_failed);
    join_any
    disable fork;
    td.check(observed, "AXI-Lite R handshake was not observed");
  endtask

  task automatic check_no_bvalid_after_first_write_channel(input int awvalid_delay,
                                                           input int wvalid_delay);
    if (awvalid_delay < wvalid_delay) begin
      wait_for_aw_handshake();
      wait_cycles();
      td.check(!target_bvalid, "B valid asserted before write data was accepted");
    end else if (wvalid_delay < awvalid_delay) begin
      wait_for_w_handshake();
      wait_cycles();
      td.check(!target_bvalid, "B valid asserted before write address was accepted");
    end
  endtask

  task automatic check_b_responses(input int num_writes);
    for (int i = 0; i < num_writes; i++) begin
      wait_for_b_handshake();
      td.check(target_bresp === ExpectedResp, "B response mismatch");
    end
    @(negedge clk);
    td.check(!target_bvalid, "B valid remained asserted after final response handshake");
  endtask

  task automatic check_r_responses(input int num_reads);
    for (int i = 0; i < num_reads; i++) begin
      wait_for_r_handshake();
      td.check(target_rdata === DefaultReadData, "R data mismatch");
      td.check(target_rresp === ExpectedResp, "R response mismatch");
    end
    @(negedge clk);
    td.check(!target_rvalid, "R valid remained asserted after final response handshake");
  endtask

  task automatic test_write_address_before_data();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.wvalid = ChannelSkewCycles;
    fork
      begin
        fork
          axil_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                          .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
          begin
            check_no_bvalid_after_first_write_channel(delays.awvalid, delays.wvalid);
            check_b_responses(NumTransactions);
          end
        join
      end
      axil_monitor.run();
    join_any
    disable fork;
  endtask

  task automatic test_write_data_before_address();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.awvalid = ChannelSkewCycles;
    fork
      begin
        fork
          axil_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                          .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
          begin
            check_no_bvalid_after_first_write_channel(delays.awvalid, delays.wvalid);
            check_b_responses(NumTransactions);
          end
        join
      end
      axil_monitor.run();
    join_any
    disable fork;
  endtask

  task automatic test_read_backpressure();
    axil_delays_t delays;

    delays = '{default: 0};
    fork
      begin
        fork
          axil_driver.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                          .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
          check_r_responses(NumTransactions);
        join
      end
      axil_monitor.run();
    join_any
    disable fork;
  endtask

  initial begin
    timeout_failed = 1'b0;
    axil_driver.init_idle();
    axil_monitor.init_idle();
    td.reset_dut();
    td.wait_cycles();

    td.check(!target_bvalid, "B valid asserted after reset");
    td.check(!target_rvalid, "R valid asserted after reset");

    test_write_address_before_data();
    test_write_data_before_address();
    test_read_backpressure();

    td.check(!driver_failed, "AXI-Lite driver reported one or more failures");
    td.check(!monitor_failed, "AXI-Lite monitor reported one or more failures");
    td.check(!timeout_failed, "Timeout reported failures");
    td.finish();
  end

endmodule : br_amba_axil_default_target_tb
