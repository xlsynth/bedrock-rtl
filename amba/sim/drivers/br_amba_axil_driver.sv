// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

// AXI-Lite target-side transaction driver.
//
// The driver owns only the target input signals and issues simple address/data/read
// request streams with configurable channel skew. Tests can combine it with a
// DUT-specific monitor to check response behavior without open-coding AXI-Lite
// handshakes in each bench.
module br_amba_axil_driver #(
    parameter int TimeoutCycles = 20
) (
    input logic clk,
    input logic rst,

    output logic target_awvalid,
    input  logic target_awready,
    output logic target_wvalid,
    input  logic target_wready,
    input  logic target_bvalid,
    output logic target_bready,
    output logic target_arvalid,
    input  logic target_arready,
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

  typedef enum int {
    WaitAwReady,
    WaitWReady,
    WaitBHandshake,
    WaitArReady,
    WaitRHandshake
  } wait_condition_e;

  localparam axil_target_inputs_t IdleTargetInputs = '{
      awvalid: 1'b0,
      wvalid: 1'b0,
      bready: 1'b0,
      arvalid: 1'b0,
      rready: 1'b0
  };
  localparam int MaxCycles = 10;

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

    random_cycles = $urandom_range(MaxCycles - 1) + 1;
    wait_cycles(random_cycles);
  endtask

  function automatic logic is_wait_condition_met(input wait_condition_e condition);
    case (condition)
      WaitAwReady: is_wait_condition_met = target_awready;
      WaitWReady: is_wait_condition_met = target_wready;
      WaitBHandshake: is_wait_condition_met = target_bvalid && target_bready;
      WaitArReady: is_wait_condition_met = target_arready;
      WaitRHandshake: is_wait_condition_met = target_rvalid && target_rready;
      default: is_wait_condition_met = 1'b0;
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

  task automatic send_aw();
    @(negedge clk);
    target_inputs.awvalid = 1'b1;
    wait_for(WaitAwReady, "Timeout waiting for AW ready");
    @(negedge clk);
    target_inputs.awvalid = 1'b0;
  endtask

  task automatic send_w();
    @(negedge clk);
    target_inputs.wvalid = 1'b1;
    wait_for(WaitWReady, "Timeout waiting for W ready");
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

  task automatic complete_b();
    wait_for(WaitBHandshake, "Timeout waiting for B handshake");
  endtask

  task automatic send_ar();
    @(negedge clk);
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

  task automatic complete_r();
    wait_for(WaitRHandshake, "Timeout waiting for R handshake");
  endtask

  task automatic issue_write_transactions(input int num_writes, input int awvalid_delay,
                                          input int wvalid_delay);
    fork
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(awvalid_delay);
          send_aw();
        end
      end
      begin
        for (int i = 0; i < num_writes; i++) begin
          wait_cycles(wvalid_delay);
          send_w();
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
          send_ar();
        end
      end
      begin
        fork
          drive_rready();
          begin
            for (int i = 0; i < num_reads; i++) begin
              complete_r();
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

endmodule : br_amba_axil_driver
