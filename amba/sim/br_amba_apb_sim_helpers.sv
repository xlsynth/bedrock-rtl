// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;

// APB requester-side transaction driver.
//
// The driver owns only the requester APB signals and applies queued setup/access/idle
// phases on the falling clock edge. Tests can call the public tasks to build precise
// APB timing scenarios without open-coding signal assignments in each bench.
module br_amba_apb_requester_driver #(
    parameter int AddrWidth = 12
) (
    input logic clk,
    input logic done,

    output logic [AddrWidth-1:0] paddr,
    output logic psel,
    output logic penable,
    output logic [ApbProtWidth-1:0] pprot,
    output logic [3:0] pstrb,
    output logic pwrite,
    output logic [31:0] pwdata
);

  typedef struct packed {
    logic [AddrWidth-1:0] addr;
    logic psel;
    logic penable;
    logic [ApbProtWidth-1:0] prot;
    logic [3:0] strb;
    logic write;
    logic [31:0] wdata;
  } apb_req_t;

  apb_req_t drive_queue[$];
  apb_req_t last_access_req;

  function automatic apb_req_t get_req(input logic [AddrWidth-1:0] addr, input logic psel_in,
                                       input logic penable_in,
                                       input logic [ApbProtWidth-1:0] prot,
                                       input logic [3:0] strb, input logic write,
                                       input logic [31:0] wdata);
    get_req.addr    = addr;
    get_req.psel    = psel_in;
    get_req.penable = penable_in;
    get_req.prot    = prot;
    get_req.strb    = strb;
    get_req.write   = write;
    get_req.wdata   = wdata;
  endfunction

  function automatic apb_req_t get_idle_req();
    get_idle_req = get_req('0, 1'b0, 1'b0, '0, '0, 1'b0, '0);
  endfunction

  function automatic void drive(input apb_req_t req);
    paddr   = req.addr;
    psel    = req.psel;
    penable = req.penable;
    pprot   = req.prot;
    pstrb   = req.strb;
    pwrite  = req.write;
    pwdata  = req.wdata;
  endfunction

  task automatic init_idle();
    last_access_req = get_idle_req();
    drive(last_access_req);
  endtask

  task automatic send_setup(input logic [AddrWidth-1:0] addr,
                            input logic [ApbProtWidth-1:0] prot, input logic [3:0] strb,
                            input logic write, input logic [31:0] wdata,
                            input int cycles = 1);
    apb_req_t setup_req;

    setup_req = get_req(addr, 1'b1, 1'b0, prot, strb, write, wdata);
    drive_queue.push_back(setup_req);
    repeat (cycles) @(negedge clk);
  endtask

  task automatic send_access(input logic [AddrWidth-1:0] addr,
                             input logic [ApbProtWidth-1:0] prot, input logic [3:0] strb,
                             input logic write, input logic [31:0] wdata);
    last_access_req = get_req(addr, 1'b1, 1'b1, prot, strb, write, wdata);
    drive_queue.push_back(last_access_req);
    @(negedge clk);
  endtask

  task automatic send_idle_from_last();
    apb_req_t idle_req;

    idle_req = last_access_req;
    idle_req.psel = 1'b0;
    idle_req.penable = 1'b0;
    drive_queue.push_back(idle_req);
  endtask

  function automatic int pending_count();
    pending_count = drive_queue.size();
  endfunction

  task automatic run();
    apb_req_t req;

    while (!done) begin
      @(negedge clk);
      if (drive_queue.size() > 0) begin
        req = drive_queue.pop_front();
        drive(req);
      end
    end
  endtask

endmodule : br_amba_apb_requester_driver


// APB completer-side response driver.
//
// The driver owns only PREADY/PRDATA/PSLVERR and can generate idle, stall, and
// completion cycles. It deliberately does not inspect request signals; individual
// tests decide when a response should appear for the DUT behavior they cover.
module br_amba_apb_completer_driver (
    input logic clk,
    input logic done,

    output logic pready,
    output logic [31:0] prdata,
    output logic pslverr
);

  typedef struct packed {
    logic ready;
    logic [31:0] rdata;
    logic slverr;
  } apb_rsp_t;

  localparam logic [31:0] StallRdataBase = 32'h5a5a_0000;

  apb_rsp_t drive_queue[$];

  function automatic apb_rsp_t get_rsp(input logic ready, input logic [31:0] rdata,
                                       input logic slverr);
    get_rsp.ready  = ready;
    get_rsp.rdata  = rdata;
    get_rsp.slverr = slverr;
  endfunction

  function automatic apb_rsp_t get_idle_rsp();
    get_idle_rsp = get_rsp(1'b0, '0, 1'b0);
  endfunction

  function automatic logic [31:0] get_stall_rdata(input int cycle);
    // Keep PRDATA recognizable during stalls so waveform/debug views show that
    // stalled-cycle data is intentionally ignored until PREADY is asserted.
    get_stall_rdata = StallRdataBase | cycle;
  endfunction

  function automatic void drive(input apb_rsp_t rsp);
    pready  = rsp.ready;
    prdata  = rsp.rdata;
    pslverr = rsp.slverr;
  endfunction

  task automatic init_idle();
    drive(get_idle_rsp());
  endtask

  task automatic reset_idle();
    drive_queue.push_back(get_idle_rsp());
  endtask

  task automatic stall(input int cycle);
    drive_queue.push_back(get_rsp(1'b0, get_stall_rdata(cycle), 1'b0));
    // The completer applies queued responses on a negedge; the second cycle lets the next
    // posedge update the DUT and lets the monitor observe the result.
    repeat (2) @(negedge clk);
  endtask

  task automatic complete(input logic [31:0] rdata, input logic slverr);
    drive_queue.push_back(get_rsp(1'b1, rdata, slverr));
    // The completer applies queued responses on a negedge; the second cycle lets the next
    // posedge update the DUT and lets the monitor observe the result.
    repeat (2) @(negedge clk);
  endtask

  function automatic int pending_count();
    pending_count = drive_queue.size();
  endfunction

  task automatic run();
    apb_rsp_t rsp;

    while (!done) begin
      @(negedge clk);
      if (drive_queue.size() > 0) begin
        rsp = drive_queue.pop_front();
        drive(rsp);
      end
    end
  endtask

endmodule : br_amba_apb_completer_driver
