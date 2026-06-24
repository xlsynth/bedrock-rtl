// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_apb_sim_pkg::*;

// Directed simulation testbench for br_amba_apb_timing_slice.
//
// Scope:
// - checks reset-visible APB outputs are idle;
// - sends one zero-wait write and one stalled read to verify payload and response data;
// - exercises the back-to-back completion path where a new setup arrives while the
//   timing slice is suppressing requester traffic after a completed access.
module br_amba_apb_timing_slice_tb;
  parameter int AddrWidth = 12;

  localparam int IdleCyclesAfterTransfer = 2;
  localparam int MaxStallCycles = 3;
  localparam int RandomSeed = 32'h1bad_f00d;
  localparam int DefaultSetupCycles = 1;
  localparam int NumWriteTransactions = 1;
  localparam int NumReadTransactions = 1;
  localparam int NumBackToBackTransactions = 2;
  localparam int BackToBackSecondSetupCycles = 2;
  localparam logic [AddrWidth-1:0] SecondAddrMask = AddrWidth'(12'h321);
  localparam logic [AddrWidth-1:0] WriteAddr = AddrWidth'(12'h124);
  localparam logic [AddrWidth-1:0] ReadAddr = AddrWidth'(12'h248);
  localparam logic [ApbProtWidth-1:0] WriteProt = 3'b010;
  localparam logic [ApbProtWidth-1:0] ReadProt = 3'b101;
  localparam logic [3:0] WriteStrb = 4'b1111;
  localparam logic [3:0] ReadStrb = 4'b0000;
  localparam logic [31:0] WriteUnusedRdata = '0;
  localparam logic [31:0] ReadUnusedWdata = '0;

  logic clk;
  logic rst;

  logic [AddrWidth-1:0] paddr_in;
  logic psel_in;
  logic penable_in;
  logic [ApbProtWidth-1:0] pprot_in;
  logic [3:0] pstrb_in;
  logic pwrite_in;
  logic [31:0] pwdata_in;
  logic [31:0] prdata_out;
  logic pready_out;
  logic pslverr_out;

  logic [AddrWidth-1:0] paddr_out;
  logic psel_out;
  logic penable_out;
  logic [ApbProtWidth-1:0] pprot_out;
  logic [3:0] pstrb_out;
  logic pwrite_out;
  logic [31:0] pwdata_out;
  logic [31:0] prdata_in;
  logic pready_in;
  logic pslverr_in;

  function automatic apb_request_t get_request(
      input logic [AddrWidth-1:0] addr, input logic [ApbProtWidth-1:0] prot, input logic [3:0] strb,
      input logic write, input logic [31:0] wdata);
    get_request.addr  = addr;
    get_request.prot  = prot;
    get_request.strb  = strb;
    get_request.write = write;
    get_request.wdata = wdata;
  endfunction

  function automatic apb_request_controls_t get_request_controls(
      input int num_transactions, input int setup_cycles, input int idle_cycles);
    get_request_controls.num_transactions = num_transactions;
    get_request_controls.setup_cycles = setup_cycles;
    get_request_controls.idle_cycles = idle_cycles;
  endfunction

  function automatic apb_response_t get_response(input logic [31:0] rdata, input logic slverr);
    get_response.ready  = 1'b1;
    get_response.rdata  = rdata;
    get_response.slverr = slverr;
  endfunction

  function automatic apb_response_controls_t get_response_controls(input int num_transactions,
                                                                   input int wait_cycles);
    get_response_controls.num_transactions = num_transactions;
    get_response_controls.wait_cycles = wait_cycles;
  endfunction

  logic monitor_enable;
  logic monitor_done;

  br_amba_apb_timing_slice #(
      .AddrWidth(AddrWidth)
  ) dut (
      .clk,
      .rst,
      .paddr_in,
      .psel_in,
      .penable_in,
      .pprot_in,
      .pstrb_in,
      .pwrite_in,
      .pwdata_in,
      .prdata_out,
      .pready_out,
      .pslverr_out,
      .paddr_out,
      .psel_out,
      .penable_out,
      .pprot_out,
      .pstrb_out,
      .pwrite_out,
      .pwdata_out,
      .prdata_in,
      .pready_in,
      .pslverr_in
  );

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  br_amba_apb_requester_driver #(
      .AddrWidth(AddrWidth),
      .TimeoutCycles(100)
  ) requester (
      .clk,
      .pready(pready_out),
      .paddr(paddr_in),
      .psel(psel_in),
      .penable(penable_in),
      .pprot(pprot_in),
      .pstrb(pstrb_in),
      .pwrite(pwrite_in),
      .pwdata(pwdata_in)
  );

  br_amba_apb_completer_driver #(
      .TimeoutCycles(100)
  ) completer (
      .clk,
      .target_psel(psel_out),
      .target_penable(penable_out),
      .pready(pready_in),
      .prdata(prdata_in),
      .pslverr(pslverr_in)
  );

  br_amba_apb_timing_slice_monitor #(
      .AddrWidth(AddrWidth)
  ) monitor (
      .clk,
      .rst,
      .enable(monitor_enable),
      .done  (monitor_done),
      .paddr_in,
      .psel_in,
      .penable_in,
      .pprot_in,
      .pstrb_in,
      .pwrite_in,
      .pwdata_in,
      .prdata_out,
      .pready_out,
      .pslverr_out,
      .paddr_out,
      .psel_out,
      .penable_out,
      .pprot_out,
      .pstrb_out,
      .pwrite_out,
      .pwdata_out,
      .prdata_in,
      .pready_in,
      .pslverr_in
  );

  task automatic run_transaction(
      input apb_request_t request, input apb_request_controls_t request_controls,
      input apb_response_t response, input apb_response_controls_t response_controls);
    for (int transaction = 0; transaction < response_controls.num_transactions; transaction++) begin
      monitor.expect_response(response.rdata + 32'(transaction), response.slverr);
    end
    fork
      requester.run(request, request_controls);
      completer.run(response, response_controls);
    join
  endtask

  task automatic test_write_transaction(input int num_transactions, input logic [31:0] wdata);
    apb_request_t request;
    apb_request_controls_t request_controls;
    apb_response_t response;
    apb_response_controls_t response_controls;

    request = get_request(WriteAddr, WriteProt, WriteStrb, 1'b1, wdata);
    request_controls =
        get_request_controls(num_transactions, DefaultSetupCycles, IdleCyclesAfterTransfer);
    response = get_response(WriteUnusedRdata, 1'b0);
    response_controls = get_response_controls(num_transactions, 0);
    run_transaction(request, request_controls, response, response_controls);
  endtask

  task automatic test_read_transaction(input int num_transactions, input logic [31:0] rdata);
    apb_request_t request;
    apb_request_controls_t request_controls;
    apb_response_t response;
    apb_response_controls_t response_controls;

    request = get_request(ReadAddr, ReadProt, ReadStrb, 1'b0, ReadUnusedWdata);
    request_controls =
        get_request_controls(num_transactions, DefaultSetupCycles, IdleCyclesAfterTransfer);
    response = get_response(rdata, 1'b1);
    response_controls = get_response_controls(num_transactions, MaxStallCycles);
    run_transaction(request, request_controls, response, response_controls);
  endtask

  task automatic test_back_to_back_same_select(input int num_transactions, input logic [31:0] wdata,
                                               input logic [31:0] rdata);
    logic [AddrWidth-1:0] first_addr;
    logic [AddrWidth-1:0] second_addr;
    apb_request_t request;
    apb_request_controls_t request_controls;
    apb_response_t response;
    apb_response_controls_t response_controls;

    td.check(num_transactions == NumBackToBackTransactions,
             "back-to-back APB scenario expects exactly two transactions");
    first_addr = '1;
    second_addr = '1 ^ SecondAddrMask;

    request = get_request(first_addr, WriteProt, WriteStrb, 1'b1, wdata);
    request_controls = get_request_controls(1, DefaultSetupCycles, 0);
    response = get_response(WriteUnusedRdata, 1'b0);
    response_controls = get_response_controls(1, 0);
    run_transaction(request, request_controls, response, response_controls);

    request = get_request(second_addr, ReadProt, ReadStrb, 1'b0, ReadUnusedWdata);
    request_controls =
        get_request_controls(1, BackToBackSecondSetupCycles, IdleCyclesAfterTransfer);
    response = get_response(rdata, 1'b1);
    response_controls = get_response_controls(1, 0);
    run_transaction(request, request_controls, response, response_controls);
  endtask

  initial begin
    int random_seed;
    logic [31:0] wdata;
    logic [31:0] rdata;

    monitor_enable = 1'b0;
    monitor_done   = 1'b0;
    random_seed    = RandomSeed;
    void'($urandom(random_seed));
    wdata = $urandom();
    rdata = $urandom();

    requester.init_idle();
    completer.init_idle();
    monitor.clear();
    td.reset_dut();
    td.wait_cycles();

    td.check(!psel_out, "psel_out asserted after reset");
    td.check(!penable_out, "penable_out asserted after reset");
    td.check(!pready_out, "pready_out asserted after reset");

    fork
      monitor.run();
    join_none

    monitor_enable = 1'b1;

    test_write_transaction(NumWriteTransactions, wdata);
    test_read_transaction(NumReadTransactions, rdata);
    test_back_to_back_same_select(NumBackToBackTransactions, wdata, rdata);

    td.check(monitor.pending_count() == 0, "monitor response queue not empty");
    td.check(monitor.get_error_count() == 0, "APB monitor reported errors");
    monitor_enable = 1'b0;
    monitor_done   = 1'b1;
    td.finish();
  end

endmodule : br_amba_apb_timing_slice_tb
