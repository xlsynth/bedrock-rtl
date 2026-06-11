// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

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
