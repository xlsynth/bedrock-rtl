// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

module br_amba_axil_default_target_tb;
  parameter int DataWidth = 32;
  parameter int ResponseKind = 2;  // 0: OKAY, 1: SLVERR, 2: DECERR

  localparam int TimeoutCycles = 20;
  localparam logic [63:0] DefaultReadDataFull = 64'hf00d_cafe_1234_5678;
  localparam logic [DataWidth-1:0] DefaultReadData = DefaultReadDataFull[DataWidth-1:0];
  localparam logic [AxiRespWidth-1:0] ExpectedResp =
      ResponseKind == 2 ? AxiRespDecerr : ResponseKind == 1 ? AxiRespSlverr : AxiRespOkay;
  localparam bit DecodeError = ResponseKind == 2;
  localparam bit SlvErr = ResponseKind == 1;

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

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  task automatic init_inputs();
    target_awvalid = 1'b0;
    target_wvalid  = 1'b0;
    target_bready  = 1'b0;
    target_arvalid = 1'b0;
    target_rready  = 1'b0;
  endtask

  task automatic check_resp(input logic [AxiRespWidth-1:0] actual, input string message);
    td.check(actual === ExpectedResp, $sformatf(
             "%s: expected 0x%0h got 0x%0h", message, ExpectedResp, actual));
  endtask

  task automatic check_data(input logic [DataWidth-1:0] actual, input string message);
    td.check(actual === DefaultReadData, $sformatf(
             "%s: expected 0x%0h got 0x%0h", message, DefaultReadData, actual));
  endtask

  task automatic wait_for_aw_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_awready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for AW ready");
  endtask

  task automatic wait_for_w_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_wready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for W ready");
  endtask

  task automatic wait_for_bvalid();
    int timeout = 0;

    @(posedge clk);
    while (!target_bvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for B valid");
  endtask

  task automatic wait_for_ar_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_arready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for AR ready");
  endtask

  task automatic wait_for_rvalid();
    int timeout = 0;

    @(posedge clk);
    while (!target_rvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    td.check(timeout < TimeoutCycles, "Timeout waiting for R valid");
  endtask

  task automatic send_aw();
    @(negedge clk);
    target_awvalid = 1'b1;
    wait_for_aw_ready();
    @(negedge clk);
    target_awvalid = 1'b0;
  endtask

  task automatic send_w();
    @(negedge clk);
    target_wvalid = 1'b1;
    wait_for_w_ready();
    @(negedge clk);
    target_wvalid = 1'b0;
  endtask

  task automatic accept_b();
    wait_for_bvalid();
    check_resp(target_bresp, "B response mismatch");
    @(negedge clk);
    target_bready = 1'b1;
    @(posedge clk);
    @(negedge clk);
    target_bready = 1'b0;
    td.wait_cycles();
    td.check(!target_bvalid, "B valid remained asserted after response handshake");
  endtask

  task automatic send_ar();
    @(negedge clk);
    target_arvalid = 1'b1;
    wait_for_ar_ready();
    @(negedge clk);
    target_arvalid = 1'b0;
  endtask

  task automatic accept_r();
    wait_for_rvalid();
    check_resp(target_rresp, "R response mismatch");
    check_data(target_rdata, "R data mismatch");
    @(negedge clk);
    target_rready = 1'b1;
    @(posedge clk);
    @(negedge clk);
    target_rready = 1'b0;
    td.wait_cycles();
    td.check(!target_rvalid, "R valid remained asserted after response handshake");
  endtask

  task automatic test_write_address_before_data();
    target_bready = 1'b0;
    send_aw();
    td.wait_cycles();
    td.check(!target_bvalid, "B valid asserted before write data was accepted");

    send_w();
    wait_for_bvalid();
    check_resp(target_bresp, "B response mismatch under backpressure");
    td.wait_cycles(2);
    td.check(target_bvalid, "B valid did not remain asserted while B ready was low");

    accept_b();
  endtask

  task automatic test_write_data_before_address();
    target_bready = 1'b0;
    send_w();
    td.wait_cycles();
    td.check(!target_bvalid, "B valid asserted before write address was accepted");

    send_aw();
    accept_b();
  endtask

  task automatic test_read_backpressure();
    target_rready = 1'b0;
    send_ar();
    wait_for_rvalid();
    check_resp(target_rresp, "R response mismatch under backpressure");
    check_data(target_rdata, "R data mismatch under backpressure");
    td.wait_cycles(2);
    td.check(target_rvalid, "R valid did not remain asserted while R ready was low");
    check_data(target_rdata, "R data changed while stalled");

    accept_r();
  endtask

  initial begin
    init_inputs();
    td.reset_dut();
    td.wait_cycles();

    td.check(!target_bvalid, "B valid asserted after reset");
    td.check(!target_rvalid, "R valid asserted after reset");

    test_write_address_before_data();
    test_write_data_before_address();
    test_read_backpressure();

    td.finish();
  end

endmodule : br_amba_axil_default_target_tb
