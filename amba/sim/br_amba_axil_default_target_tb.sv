// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

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

  br_amba_axil_driver #(
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
      .DataWidth(DataWidth),
      .ExpectedResp(ExpectedResp),
      .DefaultReadData(DefaultReadData)
  ) axil_monitor (
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
      .target_rready,
      .failed(monitor_failed)
  );

  task automatic test_write_address_before_data();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.wvalid = ChannelSkewCycles;
    fork
      axil_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
      axil_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                       .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_write_data_before_address();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.awvalid = ChannelSkewCycles;
    fork
      axil_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
      axil_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                       .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_read_backpressure();
    axil_delays_t delays;

    delays = '{default: 0};
    fork
      axil_driver.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
      axil_monitor.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                       .wvalid_delay(delays.wvalid));
    join
  endtask

  initial begin
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
    td.finish();
  end

endmodule : br_amba_axil_default_target_tb
