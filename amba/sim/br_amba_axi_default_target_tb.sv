// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

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

  br_amba_axi_default_target_driver #(
      .AxiIdWidth(AxiIdWidth),
      .SingleBeat(SingleBeat),
      .TimeoutCycles(TimeoutCycles)
  ) axi_driver (
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
      .target_arvalid,
      .target_arready,
      .target_arid,
      .target_arlen,
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

  task automatic test_write_address_before_data();
    axi_default_delays_t delays;

    delays = '{default: 0};
    delays.wvalid = ChannelSkewCycles;
    fork
      axi_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
      axi_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_write_data_before_address();
    axi_default_delays_t delays;

    delays = '{default: 0};
    delays.awvalid = ChannelSkewCycles;
    fork
      axi_driver.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
      axi_monitor.run(.num_writes(NumTransactions), .awvalid_delay(delays.awvalid),
                      .wvalid_delay(delays.wvalid));
    join
  endtask

  task automatic test_read_backpressure();
    axi_default_delays_t delays;

    delays = '{default: 0};
    fork
      axi_driver.run(.num_reads(NumTransactions), .awvalid_delay(delays.awvalid),
                     .wvalid_delay(delays.wvalid), .arvalid_delay(delays.arvalid));
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
