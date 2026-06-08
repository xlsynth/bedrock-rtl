// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

module br_amba_apb_timing_slice_tb;
  parameter int AddrWidth = 12;

  localparam int IdleCyclesAfterTransfer = 2;
  localparam int MaxStallCycles = 3;
  localparam logic [AddrWidth-1:0] SecondAddrMask = 12'h321;

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

  task automatic init_inputs();
    paddr_in   = '0;
    psel_in    = 1'b0;
    penable_in = 1'b0;
    pprot_in   = '0;
    pstrb_in   = '0;
    pwrite_in  = 1'b0;
    pwdata_in  = '0;
    prdata_in  = '0;
    pready_in  = 1'b0;
    pslverr_in = 1'b0;
  endtask

  task automatic drive_apb(input logic [AddrWidth-1:0] addr, input logic psel,
                           input logic penable, input logic [ApbProtWidth-1:0] prot,
                           input logic [3:0] strb, input logic write, input logic [31:0] wdata);
    paddr_in   = addr;
    psel_in    = psel;
    penable_in = penable;
    pprot_in   = prot;
    pstrb_in   = strb;
    pwrite_in  = write;
    pwdata_in  = wdata;
  endtask

  task automatic drive_apb_idle();
    psel_in    = 1'b0;
    penable_in = 1'b0;
  endtask

  task automatic drive_slave_response(input logic ready, input logic [31:0] rdata,
                                      input logic slverr);
    pready_in  = ready;
    prdata_in  = rdata;
    pslverr_in = slverr;
  endtask

  function automatic logic [31:0] get_stall_rdata(input int cycle);
    get_stall_rdata = 32'h5a5a_0000 | cycle;
  endfunction

  task automatic check_downstream(input logic [AddrWidth-1:0] addr,
                                  input logic expected_psel, input logic expected_penable,
                                  input logic [ApbProtWidth-1:0] prot,
                                  input logic [3:0] strb, input logic write,
                                  input logic [31:0] wdata, input string phase);
    td.check(paddr_out === addr, $sformatf("%s: paddr_out mismatch", phase));
    td.check(psel_out === expected_psel, $sformatf("%s: psel_out mismatch", phase));
    td.check(penable_out === expected_penable, $sformatf("%s: penable_out mismatch", phase));
    td.check(pprot_out === prot, $sformatf("%s: pprot_out mismatch", phase));
    td.check(pstrb_out === strb, $sformatf("%s: pstrb_out mismatch", phase));
    td.check(pwrite_out === write, $sformatf("%s: pwrite_out mismatch", phase));
    td.check(pwdata_out === wdata, $sformatf("%s: pwdata_out mismatch", phase));
  endtask

  task automatic check_response(input logic expected_pready, input logic [31:0] rdata,
                                input logic slverr, input string phase);
    td.check(pready_out === expected_pready, $sformatf("%s: pready_out mismatch", phase));
    td.check(prdata_out === rdata, $sformatf("%s: prdata_out mismatch", phase));
    td.check(pslverr_out === slverr, $sformatf("%s: pslverr_out mismatch", phase));
  endtask

  task automatic check_idle_after_transfer(input logic [AddrWidth-1:0] addr,
                                           input logic [ApbProtWidth-1:0] prot,
                                           input logic [3:0] strb, input logic write,
                                           input logic [31:0] wdata);
    for (int i = 0; i < IdleCyclesAfterTransfer; i++) begin
      drive_slave_response(1'b0, '0, 1'b0);
      td.wait_cycles();
      check_downstream(addr, 1'b0, 1'b0, prot, strb, write, wdata,
                       $sformatf("post-transfer idle cycle %0d", i));
      td.check(!pready_out, $sformatf("pready_out asserted in post-transfer idle cycle %0d", i));
    end
  endtask

  task automatic run_transaction(input logic [AddrWidth-1:0] addr,
                                 input logic [ApbProtWidth-1:0] prot,
                                 input logic [3:0] strb, input logic write,
                                 input logic [31:0] wdata, input int wait_cycles,
                                 input logic [31:0] rdata, input logic slverr);
    string phase;
    logic [31:0] stall_rdata;

    drive_slave_response(1'b0, '0, 1'b0);
    drive_apb(addr, 1'b1, 1'b0, prot, strb, write, wdata);
    td.wait_cycles();
    check_downstream(addr, 1'b1, 1'b0, prot, strb, write, wdata, "setup");
    check_response(1'b0, '0, 1'b0, "setup");

    drive_apb(addr, 1'b1, 1'b1, prot, strb, write, wdata);
    td.wait_cycles();
    check_downstream(addr, 1'b1, 1'b1, prot, strb, write, wdata, "access");
    check_response(1'b0, '0, 1'b0, "access");

    for (int i = 0; i < wait_cycles; i++) begin
      phase = $sformatf("stalled access cycle %0d", i);
      stall_rdata = get_stall_rdata(i);
      drive_slave_response(1'b0, stall_rdata, 1'b0);
      td.wait_cycles();
      check_downstream(addr, 1'b1, 1'b1, prot, strb, write, wdata, phase);
      check_response(1'b0, stall_rdata, 1'b0, phase);
    end

    drive_slave_response(1'b1, rdata, slverr);
    td.wait_cycles();
    check_downstream(addr, 1'b0, 1'b0, prot, strb, write, wdata, "ready response");
    check_response(1'b1, rdata, slverr, "ready response");

    drive_apb_idle();
    check_idle_after_transfer(addr, prot, strb, write, wdata);
  endtask

  task automatic run_back_to_back_same_select();
    logic [AddrWidth-1:0] first_addr;
    logic [AddrWidth-1:0] second_addr;

    first_addr  = '1;
    second_addr = '1 ^ SecondAddrMask;

    drive_slave_response(1'b0, '0, 1'b0);
    drive_apb(first_addr, 1'b1, 1'b0, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001);
    td.wait_cycles();
    check_downstream(first_addr, 1'b1, 1'b0, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001,
                     "back-to-back first setup");

    drive_apb(first_addr, 1'b1, 1'b1, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001);
    td.wait_cycles();
    check_downstream(first_addr, 1'b1, 1'b1, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001,
                     "back-to-back first access");

    drive_slave_response(1'b1, 32'hfeed_1001, 1'b0);
    td.wait_cycles();
    check_downstream(first_addr, 1'b0, 1'b0, 3'b001, 4'b1111, 1'b1, 32'haaaa_0001,
                     "back-to-back first response");
    check_response(1'b1, 32'hfeed_1001, 1'b0, "back-to-back first response");

    drive_slave_response(1'b0, '0, 1'b0);
    drive_apb(second_addr, 1'b1, 1'b0, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002);
    td.wait_cycles();
    check_downstream(second_addr, 1'b0, 1'b0, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002,
                     "back-to-back cooldown");
    check_response(1'b0, '0, 1'b0, "back-to-back cooldown");

    td.wait_cycles();
    check_downstream(second_addr, 1'b1, 1'b0, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002,
                     "back-to-back second setup");

    drive_apb(second_addr, 1'b1, 1'b1, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002);
    td.wait_cycles();
    check_downstream(second_addr, 1'b1, 1'b1, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002,
                     "back-to-back second access");

    drive_slave_response(1'b1, 32'hfeed_2002, 1'b1);
    td.wait_cycles();
    check_downstream(second_addr, 1'b0, 1'b0, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002,
                     "back-to-back second response");
    check_response(1'b1, 32'hfeed_2002, 1'b1, "back-to-back second response");

    drive_apb_idle();
    check_idle_after_transfer(second_addr, 3'b110, 4'b0011, 1'b0, 32'hbbbb_0002);
  endtask

  initial begin
    init_inputs();
    td.reset_dut();
    td.wait_cycles();

    td.check(!psel_out, "psel_out asserted after reset");
    td.check(!penable_out, "penable_out asserted after reset");
    td.check(!pready_out, "pready_out asserted after reset");

    run_transaction('h124, 3'b010, 4'b1111, 1'b1, 32'hc001_cafe, 0, 32'h1234_5678,
                    1'b0);
    run_transaction('h248, 3'b101, 4'b0000, 1'b0, 32'hdead_beef, MaxStallCycles,
                    32'h89ab_cdef, 1'b1);
    run_back_to_back_same_select();

    td.finish();
  end

endmodule : br_amba_apb_timing_slice_tb
