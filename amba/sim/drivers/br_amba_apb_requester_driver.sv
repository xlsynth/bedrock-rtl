// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_apb_sim_pkg::*;

// APB requester-side transaction driver.
//
// The driver owns only the requester APB signals and issues one directed APB
// transfer per run call. Tests combine it with a DUT-specific monitor to check
// response behavior without open-coding APB phase sequencing in each bench.
module br_amba_apb_requester_driver #(
    parameter int AddrWidth = 12,
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic pready,

    output logic [AddrWidth-1:0] paddr,
    output logic psel,
    output logic penable,
    output logic [ApbProtWidth-1:0] pprot,
    output logic [3:0] pstrb,
    output logic pwrite,
    output logic [31:0] pwdata
);

  apb_request_beat_t apb_beat;

  assign paddr   = apb_beat.request.addr;
  assign psel    = apb_beat.psel;
  assign penable = apb_beat.penable;
  assign pprot   = apb_beat.request.prot;
  assign pstrb   = apb_beat.request.strb;
  assign pwrite  = apb_beat.request.write;
  assign pwdata  = apb_beat.request.wdata;

  function automatic apb_request_beat_t request_beat(
      input apb_request_t request, input logic psel_value, input logic penable_value);
    request_beat.psel    = psel_value;
    request_beat.penable = penable_value;
    request_beat.request = request;
  endfunction

  task automatic init_idle();
    apb_beat = request_beat('0, Psel0, Penable0);
  endtask

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  task automatic issue_setup_request(input apb_request_t request, input int setup_cycles);
    int setup_count;

    setup_count = setup_cycles;
    if (setup_count < 1) begin
      setup_count = 1;
    end
    for (int cycle = 0; cycle < setup_count; cycle++) begin
      @(negedge clk);
      apb_beat = request_beat(request, Psel1, Penable0);
    end
  endtask

  task automatic issue_access_request(input apb_request_t request);
    @(negedge clk);
    apb_beat = request_beat(request, Psel1, Penable1);
  endtask

  task automatic wait_for_response();
    int timeout = 0;

    @(posedge clk);
    while (!pready && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end
    if (!pready) begin
      $error("Timeout waiting for upstream APB response");
    end
  endtask

  task automatic drive_idle(input int idle_cycles);
    if (idle_cycles > 0) begin
      wait_for_response();
      @(negedge clk);
      apb_beat.psel    = Psel0;
      apb_beat.penable = Penable0;
      wait_cycles(idle_cycles - 1);
    end
  endtask

  task automatic run(input apb_request_t inputs, input apb_request_controls_t controls);
    apb_request_t request;

    for (int transaction = 0; transaction < controls.num_transactions; transaction++) begin
      request.addr  = AddrWidth'(inputs.addr + AddrWidth'(transaction));
      request.prot  = inputs.prot;
      request.strb  = inputs.strb;
      request.write = inputs.write;
      request.wdata = inputs.wdata + 32'(transaction);
      issue_setup_request(request, controls.setup_cycles);
      issue_access_request(request);
      drive_idle(controls.idle_cycles);
    end
  endtask

endmodule : br_amba_apb_requester_driver
