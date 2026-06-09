// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

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
  localparam logic [AddrWidth-1:0] SecondAddrMask = 12'h321;
  localparam int RandomSeed = 32'h1bad_f00d;
  localparam logic [AddrWidth-1:0] WriteAddr = 'h124;
  localparam logic [AddrWidth-1:0] ReadAddr = 'h248;
  localparam logic [ApbProtWidth-1:0] WriteProt = 3'b010;
  localparam logic [ApbProtWidth-1:0] ReadProt = 3'b101;
  localparam logic [3:0] WriteStrb = 4'b1111;
  localparam logic [3:0] ReadStrb = 4'b0000;

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

  logic monitor_enable;
  logic monitor_done;
  logic driver_done;

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
      .AddrWidth(AddrWidth)
  ) requester (
      .clk,
      .done(driver_done),
      .paddr(paddr_in),
      .psel(psel_in),
      .penable(penable_in),
      .pprot(pprot_in),
      .pstrb(pstrb_in),
      .pwrite(pwrite_in),
      .pwdata(pwdata_in)
  );

  br_amba_apb_completer_driver completer (
      .clk,
      .done(driver_done),
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
      .done(monitor_done),
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

  task automatic wait_idle_after_transfer();
    requester.send_idle_from_last();
    for (int i = 0; i < IdleCyclesAfterTransfer; i++) begin
      // Drive the completer idle while the requester side drains the timing-slice cooldown.
      completer.reset_idle();
      td.wait_cycles();
    end
  endtask

  task automatic send_transaction(input logic [AddrWidth-1:0] addr,
                                  input logic [ApbProtWidth-1:0] prot,
                                  input logic [3:0] strb, input logic write,
                                  input logic [31:0] wdata, input int wait_cycles,
                                  input logic [31:0] rdata, input logic slverr,
                                  input string phase = "ready response");
    requester.send_setup(addr, prot, strb, write, wdata);
    requester.send_access(addr, prot, strb, write, wdata);

    for (int i = 0; i < wait_cycles; i++) begin
      completer.stall(i);
    end

    monitor.expect_response(rdata, slverr, phase);
    completer.complete(rdata, slverr);
    wait_idle_after_transfer();
  endtask

  // Complete an access and immediately start another transfer while the timing slice is
  // suppressing requester traffic. This covers the cooldown path that prevents a new
  // setup phase from leaking through in the response cycle after a completed access.
  task automatic run_back_to_back_same_select();
    logic [AddrWidth-1:0] first_addr;
    logic [AddrWidth-1:0] second_addr;

    first_addr  = '1;
    second_addr = '1 ^ SecondAddrMask;

    completer.reset_idle();
    requester.send_setup(first_addr, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001);
    requester.send_access(first_addr, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001);
    // Leave the requester in access after the first response to exercise the slice cooldown.
    monitor.expect_response(32'hfeed_1001, 1'b0, "back-to-back first response");
    completer.complete(32'hfeed_1001, 1'b0);

    completer.reset_idle();
    // The second setup is driven during cooldown. The two-cycle wait checks that the DUT
    // suppresses PSEL for the response cycle and the following valid_handshake_d1 cycle.
    requester.send_setup(second_addr, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002, 2);
    requester.send_access(second_addr, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002);
    monitor.expect_response(32'hfeed_2002, 1'b1, "back-to-back second response");
    completer.complete(32'hfeed_2002, 1'b1);
    wait_idle_after_transfer();
  endtask

  initial begin
    int random_seed;
    logic [31:0] write_wdata;
    logic [31:0] write_rdata;
    logic [31:0] read_wdata;
    logic [31:0] read_rdata;

    monitor_enable = 1'b0;
    monitor_done   = 1'b0;
    driver_done    = 1'b0;
    random_seed    = RandomSeed;
    void'($urandom(random_seed));
    write_wdata = $urandom();
    write_rdata = $urandom();
    read_wdata  = $urandom();
    read_rdata  = $urandom();

    requester.init_idle();
    completer.init_idle();
    monitor.clear();
    td.reset_dut();
    td.wait_cycles();

    td.check(!psel_out, "psel_out asserted after reset");
    td.check(!penable_out, "penable_out asserted after reset");
    td.check(!pready_out, "pready_out asserted after reset");

    fork
      requester.run();
      completer.run();
      monitor.run();
    join_none

    monitor_enable = 1'b1;

    send_transaction(WriteAddr, WriteProt, WriteStrb, 1'b1, write_wdata, 0, write_rdata, 1'b0);
    send_transaction(ReadAddr, ReadProt, ReadStrb, 1'b0, read_wdata, MaxStallCycles, read_rdata,
                     1'b1);
    run_back_to_back_same_select();

    td.check(requester.pending_count() == 0, "requester drive queue not empty");
    td.check(completer.pending_count() == 0, "completer drive queue not empty");
    td.check(monitor.pending_count() == 0, "monitor response queue not empty");
    td.check(monitor.get_error_count() == 0, "APB monitor reported errors");
    monitor_enable = 1'b0;
    monitor_done   = 1'b1;
    driver_done    = 1'b1;
    td.finish();
  end

endmodule : br_amba_apb_timing_slice_tb
