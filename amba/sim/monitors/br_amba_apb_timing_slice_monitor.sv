// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_apb_sim_pkg::*;

// APB timing-slice reference monitor.
//
// This is not a generic APB bus monitor. A generic monitor would only observe one APB
// interface and report accepted transfers. This monitor checks the specific
// br_amba_apb_timing_slice transform between two APB interfaces: request signals pass
// through except while a downstream access completes, PSEL/PENABLE are suppressed for
// the completion cycle and the following cooldown cycle, and requester responses are
// produced from the previous downstream valid handshake. Use this monitor only for a
// DUT with the same timing-slice contract; reuse the requester/completer drivers for
// other APB DUTs with a DUT-specific monitor or scoreboard.
module br_amba_apb_timing_slice_monitor #(
    parameter int AddrWidth = 12
) (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic done,

    input logic [AddrWidth-1:0] paddr_in,
    input logic psel_in,
    input logic penable_in,
    input logic [ApbProtWidth-1:0] pprot_in,
    input logic [3:0] pstrb_in,
    input logic pwrite_in,
    input logic [31:0] pwdata_in,
    input logic [31:0] prdata_out,
    input logic pready_out,
    input logic pslverr_out,

    input logic [AddrWidth-1:0] paddr_out,
    input logic psel_out,
    input logic penable_out,
    input logic [ApbProtWidth-1:0] pprot_out,
    input logic [3:0] pstrb_out,
    input logic pwrite_out,
    input logic [31:0] pwdata_out,
    input logic [31:0] prdata_in,
    input logic pready_in,
    input logic pslverr_in
);

  apb_response_t expected_rsp_queue[$];
  int error_count;

  function automatic apb_request_beat_t get_req(
      input logic [AddrWidth-1:0] addr, input logic psel, input logic penable,
      input logic [ApbProtWidth-1:0] prot, input logic [3:0] strb, input logic write,
      input logic [31:0] wdata);
    get_req.psel          = psel;
    get_req.penable       = penable;
    get_req.request.addr  = 32'(addr);
    get_req.request.prot  = prot;
    get_req.request.strb  = strb;
    get_req.request.write = write;
    get_req.request.wdata = wdata;
  endfunction

  function automatic apb_response_t get_rsp(input logic ready, input logic [31:0] rdata,
                                            input logic slverr);
    get_rsp.ready  = ready;
    get_rsp.rdata  = rdata;
    get_rsp.slverr = slverr;
  endfunction

  task automatic check(input logic condition, input string message);
    if (!condition) begin
      error_count++;
      $error("%s", message);
    end
  endtask

  task automatic clear();
    error_count = 0;
    expected_rsp_queue.delete();
  endtask

  task automatic expect_response(input logic [31:0] rdata, input logic slverr);
    expected_rsp_queue.push_back(get_rsp(Pready1, rdata, slverr));
  endtask

  task automatic read_downstream(output apb_request_beat_t req);
    req = get_req(paddr_out, psel_out, penable_out, pprot_out, pstrb_out, pwrite_out, pwdata_out);
  endtask

  task automatic read_response(output apb_response_t rsp);
    rsp = get_rsp(pready_out, prdata_out, pslverr_out);
  endtask

  task automatic check_downstream(input apb_request_beat_t actual,
                                  input apb_request_beat_t expected, input string phase);
    check(actual.psel === expected.psel, $sformatf("%s: psel_out mismatch", phase));
    check(actual.penable === expected.penable, $sformatf("%s: penable_out mismatch", phase));
    check(actual.request.addr === expected.request.addr, $sformatf("%s: paddr_out mismatch", phase
          ));
    check(actual.request.prot === expected.request.prot, $sformatf("%s: pprot_out mismatch", phase
          ));
    check(actual.request.strb === expected.request.strb, $sformatf("%s: pstrb_out mismatch", phase
          ));
    check(actual.request.write === expected.request.write, $sformatf(
          "%s: pwrite_out mismatch", phase));
    check(actual.request.wdata === expected.request.wdata, $sformatf(
          "%s: pwdata_out mismatch", phase));
  endtask

  task automatic check_response(input apb_response_t actual, input apb_response_t expected);
    check(actual.ready === expected.ready, "pready_out mismatch");

    if (expected.ready || actual.ready) begin
      check(actual.rdata === expected.rdata, $sformatf(
            "prdata_out mismatch, got 0x%08x expected 0x%08x", actual.rdata, expected.rdata));
      check(actual.slverr === expected.slverr, $sformatf(
            "pslverr_out mismatch, got %0b expected %0b", actual.slverr, expected.slverr));
    end
  endtask

  function automatic int pending_count();
    pending_count = expected_rsp_queue.size();
  endfunction

  function automatic int get_error_count();
    get_error_count = error_count;
  endfunction

  task automatic run();
    apb_request_beat_t actual_req;
    apb_request_beat_t expected_req;
    apb_response_t actual_rsp;
    apb_response_t expected_rsp;
    // Expected downstream APB state from the previous monitor cycle.
    logic expected_psel_out;
    logic expected_penable_out;
    logic expected_valid_handshake_d1;
    logic valid_handshake;

    expected_psel_out = Psel0;
    expected_penable_out = Penable0;
    expected_valid_handshake_d1 = Pready0;

    while (!done) begin
      @(posedge clk);
      // Sample after the DUT's posedge-triggered updates have settled so the monitor
      // checks the same-cycle APB outputs rather than the previous cycle's values.
      #1ps;
      if (enable && !rst) begin
        valid_handshake = expected_psel_out && expected_penable_out && pready_in;

        expected_req = get_req(
            paddr_in,
            psel_in && !valid_handshake && !expected_valid_handshake_d1,
            penable_in && !valid_handshake && !expected_valid_handshake_d1,
            pprot_in,
            pstrb_in,
            pwrite_in,
            pwdata_in
        );

        read_downstream(actual_req);
        check_downstream(actual_req, expected_req, "downstream monitor");

        read_response(actual_rsp);
        check(actual_rsp.ready === valid_handshake, "pready_out mismatch in response monitor");

        if (actual_rsp.ready) begin
          check(expected_rsp_queue.size() > 0, "unexpected APB response");
          if (expected_rsp_queue.size() > 0) begin
            expected_rsp = expected_rsp_queue.pop_front();
            check_response(actual_rsp, expected_rsp);
          end
        end

        expected_psel_out = expected_req.psel;
        expected_penable_out = expected_req.penable;
        expected_valid_handshake_d1 = valid_handshake;
      end
    end
  endtask

endmodule : br_amba_apb_timing_slice_monitor
