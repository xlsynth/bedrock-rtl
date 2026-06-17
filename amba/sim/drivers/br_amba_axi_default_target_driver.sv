// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

// AXI target-side transaction driver for br_amba_axi_default_target.
//
// The driver owns only the reduced AXI target input signals and issues address,
// write-data-last, and read request streams with configurable channel skew.
module br_amba_axi_default_target_driver #(
    parameter int AxiIdWidth = 2,
    parameter bit SingleBeat = 0,
    parameter int TimeoutCycles = 20,
    localparam int AxiLenWidth = SingleBeat ? 1 : AxiBurstLenWidth
) (
    input logic clk,
    input logic rst,

    output logic target_awvalid,
    input logic target_awready,
    output logic [AxiIdWidth-1:0] target_awid,
    output logic [AxiLenWidth-1:0] target_awlen,
    output logic target_wvalid,
    input logic target_wready,
    output logic target_wlast,
    input logic target_bvalid,
    output logic target_bready,
    output logic target_arvalid,
    input logic target_arready,
    output logic [AxiIdWidth-1:0] target_arid,
    output logic [AxiLenWidth-1:0] target_arlen,
    input logic target_rvalid,
    output logic target_rready,

    output logic failed
);

  typedef struct packed {
    logic awvalid;
    logic [AxiIdWidth-1:0] awid;
    logic [AxiLenWidth-1:0] awlen;
    logic wvalid;
    logic wlast;
    logic bready;
    logic arvalid;
    logic [AxiIdWidth-1:0] arid;
    logic [AxiLenWidth-1:0] arlen;
    logic rready;
  } axi_target_inputs_t;

  typedef enum int {
    WaitAwReady,
    WaitWReady,
    WaitBHandshake,
    WaitArReady,
    WaitRHandshake
  } wait_condition_e;

  localparam axi_target_inputs_t IdleTargetInputs = '{
      awvalid: 1'b0,
      awid: '0,
      awlen: '0,
      wvalid: 1'b0,
      wlast: 1'b0,
      bready: 1'b0,
      arvalid: 1'b0,
      arid: '0,
      arlen: '0,
      rready: 1'b0
  };
  localparam int MaxCycles = 10;
  localparam int MaxReadLen = 3;

  axi_target_inputs_t target_inputs;

  assign target_awvalid = target_inputs.awvalid;
  assign target_awid    = target_inputs.awid;
  assign target_awlen   = target_inputs.awlen;
  assign target_wvalid  = target_inputs.wvalid;
  assign target_wlast   = target_inputs.wlast;
  assign target_bready  = target_inputs.bready;
  assign target_arvalid = target_inputs.arvalid;
  assign target_arid    = target_inputs.arid;
  assign target_arlen   = target_inputs.arlen;
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

    random_cycles = $urandom_range(MaxCycles - 1) + 1;
    wait_cycles(random_cycles);
  endtask

  function automatic logic [AxiIdWidth-1:0] get_id(input int index);
    get_id = AxiIdWidth'(index + 1);
  endfunction

  function automatic logic [AxiLenWidth-1:0] get_aw_len(input int index);
    if (SingleBeat) begin
      get_aw_len = '0;
    end else begin
      get_aw_len = AxiLenWidth'(index % (MaxReadLen + 1));
    end
  endfunction

  function automatic logic [AxiLenWidth-1:0] get_ar_len(input int index);
    if (SingleBeat) begin
      get_ar_len = '0;
    end else begin
      get_ar_len = AxiLenWidth'((index % MaxReadLen) + 1);
    end
  endfunction

  function automatic logic is_wait_condition_met(input wait_condition_e condition);
    case (condition)
      WaitAwReady:    is_wait_condition_met = target_awvalid && target_awready;
      WaitWReady:     is_wait_condition_met = target_wvalid && target_wready;
      WaitBHandshake: is_wait_condition_met = target_bvalid && target_bready;
      WaitArReady:    is_wait_condition_met = target_arvalid && target_arready;
      WaitRHandshake: is_wait_condition_met = target_rvalid && target_rready;
      default:        is_wait_condition_met = 1'b0;
    endcase
  endfunction

  task automatic wait_for(input wait_condition_e condition, input string timeout_message);
    int timeout = 0;

    @(posedge clk);
    while (!is_wait_condition_met(
        condition
    ) && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    check(is_wait_condition_met(condition), timeout_message);
  endtask

  task automatic send_aw(input int index);
    @(negedge clk);
    target_inputs.awid = get_id(index);
    target_inputs.awlen = get_aw_len(index);
    target_inputs.awvalid = 1'b1;
    wait_for(WaitAwReady, "Timeout waiting for AW ready");
    @(negedge clk);
    target_inputs.awvalid = 1'b0;
  endtask

  task automatic send_wlast();
    @(negedge clk);
    target_inputs.wlast  = 1'b1;
    target_inputs.wvalid = 1'b1;
    wait_for(WaitWReady, "Timeout waiting for W ready");
    @(negedge clk);
    target_inputs.wvalid = 1'b0;
    target_inputs.wlast  = 1'b0;
  endtask

  task automatic drive_bready();
    forever begin
      wait_random_cycles();
      target_inputs.bready = 1'b1;
      wait_random_cycles();
      target_inputs.bready = 1'b0;
    end
  endtask

  task automatic complete_b();
    wait_for(WaitBHandshake, "Timeout waiting for B handshake");
  endtask

  task automatic send_ar(input int index);
    @(negedge clk);
    target_inputs.arid = get_id(index);
    target_inputs.arlen = get_ar_len(index);
    target_inputs.arvalid = 1'b1;
    wait_for(WaitArReady, "Timeout waiting for AR ready");
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

  task automatic complete_r_burst(input int index);
    int unsigned num_beats;

    num_beats = int'(get_ar_len(index)) + 1;
    for (int beat = 0; beat < num_beats; beat++) begin
      wait_for(WaitRHandshake, "Timeout waiting for R handshake");
    end
  endtask

  task automatic issue_write_transactions(input int num_writes, input int awvalid_delay,
                                          input int wvalid_delay);
    fork
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(awvalid_delay);
          send_aw(i);
        end
      end
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(wvalid_delay);
          send_wlast();
        end
      end
      begin
        fork
          drive_bready();
          begin
            for (int i = 0; i < num_writes; i++) begin
              complete_b();
            end
          end
        join_any
        disable fork;
      end
    join
  endtask

  task automatic issue_read_transactions(input int num_reads, input int arvalid_delay);
    fork
      begin
        for (int i = 0; i < num_reads; i++) begin
          wait_cycles(arvalid_delay);
          send_ar(i);
        end
      end
      begin
        fork
          drive_rready();
          begin
            for (int i = 0; i < num_reads; i++) begin
              complete_r_burst(i);
            end
          end
        join_any
        disable fork;
      end
    join
  endtask

  task automatic run(input int num_writes = 0, input int num_reads = 0, input int awvalid_delay = 0,
                     input int wvalid_delay = 0, input int arvalid_delay = 0);
    target_inputs.bready = 1'b0;
    target_inputs.rready = 1'b0;

    fork
      begin
        if (num_writes > 0) begin
          issue_write_transactions(num_writes, awvalid_delay, wvalid_delay);
        end
      end
      begin
        if (num_reads > 0) begin
          issue_read_transactions(num_reads, arvalid_delay);
        end
      end
    join

    wait_cycles();
  endtask

endmodule : br_amba_axi_default_target_driver
