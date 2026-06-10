// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

typedef enum int {
  ResponseKindOkay = 0,
  ResponseKindSlverr = 1,
  ResponseKindDecerr = 2
} response_kind_e;

typedef struct {
  int awvalid;
  int wvalid;
  int arvalid;
  int bready;
  int rready;
} axil_delays_t;

module br_amba_axil_driver #(
    parameter int DataWidth = 32,
    parameter int TimeoutCycles = 20,
    parameter logic [AxiRespWidth-1:0] ExpectedResp = AxiRespDecerr,
    parameter logic [DataWidth-1:0] DefaultReadData = '0
) (
    input logic clk,
    input logic rst,

    output logic target_awvalid,
    input  logic target_awready,
    output logic target_wvalid,
    input  logic target_wready,
    input  logic [AxiRespWidth-1:0] target_bresp,
    input  logic target_bvalid,
    output logic target_bready,
    output logic target_arvalid,
    input  logic target_arready,
    input  logic [DataWidth-1:0] target_rdata,
    input  logic [AxiRespWidth-1:0] target_rresp,
    input  logic target_rvalid,
    output logic target_rready,

    output logic failed
);

  typedef struct packed {
    logic awvalid;
    logic wvalid;
    logic bready;
    logic arvalid;
    logic rready;
  } axil_target_inputs_t;

  localparam axil_target_inputs_t IdleTargetInputs = '{
      awvalid: 1'b0,
      wvalid:  1'b0,
      bready:  1'b0,
      arvalid: 1'b0,
      rready:  1'b0
  };
  localparam int MaxReadyRandomCycles = 2;

  axil_target_inputs_t target_inputs;

  assign target_awvalid = target_inputs.awvalid;
  assign target_wvalid  = target_inputs.wvalid;
  assign target_bready  = target_inputs.bready;
  assign target_arvalid = target_inputs.arvalid;
  assign target_rready  = target_inputs.rready;

  task automatic init_idle();
    target_inputs = IdleTargetInputs;
    failed = 1'b0;
  endtask

  task automatic check(input logic condition, input string message = "Check failed");
    if (!condition) begin
      failed = 1'b1;
      $error("%s", message);
    end
  endtask

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  task automatic wait_random_cycles();
    int random_cycles;

    random_cycles = $urandom_range(MaxReadyRandomCycles - 1) + 1;
    wait_cycles(random_cycles);
  endtask

  task automatic wait_for_aw_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_awready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for AW ready");
  endtask

  task automatic wait_for_w_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_wready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for W ready");
  endtask

  task automatic wait_for_bvalid();
    int timeout = 0;

    @(posedge clk);
    while (!target_bvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for B valid");
  endtask

  task automatic wait_for_b_handshake();
    int timeout = 0;

    @(posedge clk);
    while (!(target_bvalid && target_bready) && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for B handshake");
  endtask

  task automatic wait_for_ar_ready();
    int timeout = 0;

    @(posedge clk);
    while (!target_arready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for AR ready");
  endtask

  task automatic wait_for_rvalid();
    int timeout = 0;

    @(posedge clk);
    while (!target_rvalid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for R valid");
  endtask

  task automatic wait_for_r_handshake();
    int timeout = 0;

    @(posedge clk);
    while (!(target_rvalid && target_rready) && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(timeout < TimeoutCycles, "Timeout waiting for R handshake");
  endtask

  task automatic send_aw();
    @(negedge clk);
    target_inputs.awvalid = 1'b1;
    wait_for_aw_ready();
    @(negedge clk);
    target_inputs.awvalid = 1'b0;
  endtask

  task automatic send_w();
    @(negedge clk);
    target_inputs.wvalid = 1'b1;
    wait_for_w_ready();
    @(negedge clk);
    target_inputs.wvalid = 1'b0;
  endtask

  task automatic drive_bready();
    forever begin
      wait_random_cycles();
      target_inputs.bready = 1'b1;
      wait_random_cycles();
      target_inputs.bready = 1'b0;
    end
  endtask

  task automatic complete_b(input axil_delays_t delays, input bit is_final);
    wait_for_b_handshake();
    check(target_bresp === ExpectedResp, $sformatf(
      "%s: expected 0x%0h got 0x%0h",
      delays.bready > 0 ? "B response mismatch under backpressure" : "B response mismatch",
      ExpectedResp, target_bresp));
    wait_cycles();
    if (is_final) begin
      check(!target_bvalid, "B valid remained asserted after response handshake");
    end
  endtask

  task automatic send_ar();
    @(negedge clk);
    target_inputs.arvalid = 1'b1;
    wait_for_ar_ready();
    @(negedge clk);
    target_inputs.arvalid = 1'b0;
  endtask

  task automatic drive_rready();
    forever begin
      wait_random_cycles();
      target_inputs.rready = 1'b1;
      wait_random_cycles();
      target_inputs.rready = 1'b0;
    end
  endtask

  task automatic complete_r(input axil_delays_t delays, input bit is_final);
    wait_for_r_handshake();
    check(target_rresp === ExpectedResp, $sformatf(
          "%s: expected 0x%0h got 0x%0h",
          delays.rready > 0 ? "R response mismatch under backpressure" : "R response mismatch",
          ExpectedResp, target_rresp));
    check(target_rdata === DefaultReadData, $sformatf(
          "%s: expected 0x%0h got 0x%0h",
          delays.rready > 0 ? "R data mismatch under backpressure" : "R data mismatch",
          DefaultReadData, target_rdata));
    wait_cycles();
    if (is_final) begin
      check(!target_rvalid, "R valid remained asserted after response handshake");
    end
  endtask

  task automatic check_no_bvalid_after_first_write_channel(input axil_delays_t delays);
    if (delays.awvalid < delays.wvalid) begin
      wait (target_awvalid && target_awready);
      wait_cycles();
      check(!target_bvalid, "B valid asserted before write data was accepted");
    end else if (delays.wvalid < delays.awvalid) begin
      wait (target_wvalid && target_wready);
      wait_cycles();
      check(!target_bvalid, "B valid asserted before write address was accepted");
    end
  endtask

  task automatic issue_write_transactions(input int num_writes, input axil_delays_t delays);
    fork
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(delays.awvalid);
          send_aw();
        end
      end
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(delays.wvalid);
          send_w();
        end
      end
      begin
        // A write response is only legal after both AW and W handshakes complete.
        check_no_bvalid_after_first_write_channel(delays);
      end
      begin
        fork
          drive_bready();
          begin
            for (int i = 0; i < num_writes; i++) begin
              complete_b(delays, i == num_writes - 1);
            end
          end
        join_any
        disable fork;
      end
    join
  endtask

  task automatic issue_read_transactions(input int num_reads, input axil_delays_t delays);
    fork
      begin
        for (int i = 0; i < num_reads; i++) begin
          wait_cycles(delays.arvalid);
          send_ar();
        end
      end
      begin
        fork
          drive_rready();
          begin
            for (int i = 0; i < num_reads; i++) begin
              complete_r(delays, i == num_reads - 1);
            end
          end
        join_any
        disable fork;
      end
    join
  endtask

  task automatic run(input int num_writes = 0, input int num_reads = 0,
                     input axil_delays_t delays = '{default: 0});
    target_inputs.bready = 1'b0;
    target_inputs.rready = 1'b0;

    fork
      begin
        if (num_writes > 0) begin
          issue_write_transactions(num_writes, delays);
        end
      end
      begin
        if (num_reads > 0) begin
          issue_read_transactions(num_reads, delays);
        end
      end
    join
  endtask

endmodule : br_amba_axil_driver


module br_amba_axil_default_target_tb;
  parameter int DataWidth = 32;
  parameter int NumTransactions = 1;
  parameter response_kind_e ResponseKind = ResponseKindDecerr;

  localparam int TimeoutCycles = 20;
  localparam int ChannelSkewCycles = 3;
  localparam int BackpressureCycles = 2;
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
      .DataWidth(DataWidth),
      .TimeoutCycles(TimeoutCycles),
      .ExpectedResp(ExpectedResp),
      .DefaultReadData(DefaultReadData)
  ) axil_driver (
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
      .failed(driver_failed)
  );

  task automatic test_write_address_before_data();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.wvalid = ChannelSkewCycles;
    delays.bready = BackpressureCycles;
    axil_driver.run(.num_writes(NumTransactions), .delays(delays));
  endtask

  task automatic test_write_data_before_address();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.awvalid = ChannelSkewCycles;
    axil_driver.run(.num_writes(NumTransactions), .delays(delays));
  endtask

  task automatic test_read_backpressure();
    axil_delays_t delays;

    delays = '{default: 0};
    delays.rready = BackpressureCycles;
    axil_driver.run(.num_reads(NumTransactions), .delays(delays));
  endtask

  initial begin
    axil_driver.init_idle();
    td.reset_dut();
    td.wait_cycles();

    td.check(!target_bvalid, "B valid asserted after reset");
    td.check(!target_rvalid, "R valid asserted after reset");

    test_write_address_before_data();
    test_write_data_before_address();
    test_read_backpressure();

    td.check(!driver_failed, "AXI-Lite driver reported one or more failures");
    td.finish();
  end

endmodule : br_amba_axil_default_target_tb
