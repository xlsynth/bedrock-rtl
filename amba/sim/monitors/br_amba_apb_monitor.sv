// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_apb_sim_pkg::*;

// APB protocol monitor.
//
// This monitor samples APB transfers according to PSEL/PENABLE/PREADY and checks
// protocol-level APB sequencing rules.
module br_amba_apb_monitor #(
    parameter  int AddrWidth = 12,
    parameter  int DataWidth = 32,
    localparam int StrbWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic [AddrWidth-1:0] paddr,
    input logic psel,
    input logic penable,
    input logic [ApbProtWidth-1:0] pprot,
    input logic [StrbWidth-1:0] pstrb,
    input logic pwrite,
    input logic [DataWidth-1:0] pwdata,
    input logic [DataWidth-1:0] prdata,
    input logic pready,
    input logic pslverr,

    output logic failed
);

  apb_transfer_observation_t transfer_queue[$];
  logic request_phase_seen;

  clocking cb @(posedge clk);
    default input #1step;
    input rst;
    input paddr;
    input psel;
    input penable;
    input pprot;
    input pstrb;
    input pwrite;
    input pwdata;
    input prdata;
    input pready;
    input pslverr;
  endclocking

  task automatic init_idle();
    failed = 1'b0;
    request_phase_seen = 1'b0;
    transfer_queue.delete();
  endtask

  task automatic monitor_transfers();
    apb_transfer_observation_t transfer;
    logic transfer_active = 1'b0;

    forever begin
      @cb;
      if (cb.rst) begin
        transfer_active = 1'b0;
      end else if (cb.psel && !transfer_active) begin
        transfer.request_timestamp = $time;
        transfer_active = 1'b1;
      end

      if (!cb.rst && cb.psel) begin
        request_phase_seen = 1'b1;
      end
      if (!cb.rst && cb.psel && cb.penable && cb.pready) begin
        transfer.packet.addr = ApbAddrWidth'(cb.paddr);
        transfer.packet.prot = cb.pprot;
        transfer.packet.strb = ApbStrbWidth'(cb.pstrb);
        transfer.packet.write = cb.pwrite;
        transfer.packet.data = cb.pwrite ? ApbDataWidth'(cb.pwdata) : ApbDataWidth'(cb.prdata);
        transfer.packet.slverr = cb.pslverr;
        transfer.completion_timestamp = $time;
        transfer_queue.push_back(transfer);
        transfer_active = 1'b0;
      end
    end
  endtask

  task automatic monitor_protocol();
    logic [AddrWidth-1:0] prev_paddr = '0;
    logic [ApbProtWidth-1:0] prev_pprot = '0;
    logic [StrbWidth-1:0] prev_pstrb = '0;
    logic prev_pwrite = 1'b0;
    logic [DataWidth-1:0] prev_pwdata = '0;
    logic [AddrWidth-1:0] setup_paddr = '0;
    logic [ApbProtWidth-1:0] setup_pprot = '0;
    logic [StrbWidth-1:0] setup_pstrb = '0;
    logic setup_pwrite = 1'b0;
    logic [DataWidth-1:0] setup_pwdata = '0;
    logic setup_seen = 1'b0;
    logic setup_payload_changed;
    logic prev_psel = 1'b0;
    logic prev_penable = 1'b0;
    logic access_wait = 1'b0;

    forever begin
      @cb;
      if (cb.rst) begin
        prev_psel = 1'b0;
        prev_penable = 1'b0;
        access_wait = 1'b0;
        setup_seen = 1'b0;
      end else begin
        if (cb.penable && !cb.psel) begin
          failed = 1'b1;
          $error("APB PENABLE asserted without PSEL");
        end

        if (cb.psel && !cb.penable && prev_psel && !prev_penable) begin
          failed = 1'b1;
          $error("APB setup phase lasted more than one cycle");
        end

        if (cb.psel && cb.penable && !(access_wait || (prev_psel && !prev_penable))) begin
          failed = 1'b1;
          $error("APB access phase observed without a preceding setup phase");
        end

        if (cb.psel && cb.penable && setup_seen) begin
          setup_payload_changed = cb.paddr !== setup_paddr;
          setup_payload_changed |= cb.pprot !== setup_pprot;
          setup_payload_changed |= cb.pwrite !== setup_pwrite;
          setup_payload_changed |= setup_pwrite && cb.pstrb !== setup_pstrb;
          setup_payload_changed |= setup_pwrite && cb.pwdata !== setup_pwdata;

          if (setup_payload_changed) begin
            failed = 1'b1;
            $error("APB request signals changed between setup and access phase");
          end
        end

        // During APB wait states, request/control payload must remain stable
        // until the transfer completes with PREADY. Write data and strobes are
        // significant only for write transfers.
        if (access_wait && !(cb.psel && cb.penable)) begin
          failed = 1'b1;
          $error("APB access phase ended before PREADY");
        end else if (access_wait) begin
          if (cb.paddr !== prev_paddr || cb.pprot !== prev_pprot || cb.pwrite !== prev_pwrite ||
              (prev_pwrite && (cb.pstrb !== prev_pstrb || cb.pwdata !== prev_pwdata))) begin
            failed = 1'b1;
            $error("APB request signals changed while PREADY was low");
          end
        end

        access_wait = cb.psel && cb.penable && !cb.pready;
        if (access_wait) begin
          prev_paddr  = cb.paddr;
          prev_pprot  = cb.pprot;
          prev_pstrb  = cb.pstrb;
          prev_pwrite = cb.pwrite;
          prev_pwdata = cb.pwdata;
        end
        if (cb.psel && !cb.penable) begin
          setup_paddr  = cb.paddr;
          setup_pprot  = cb.pprot;
          setup_pstrb  = cb.pstrb;
          setup_pwrite = cb.pwrite;
          setup_pwdata = cb.pwdata;
          setup_seen   = 1'b1;
        end else if (cb.psel && cb.penable) begin
          setup_seen = 1'b0;
        end else begin
          setup_seen = 1'b0;
        end
        prev_psel = cb.psel;
        prev_penable = cb.penable;
      end
    end
  endtask

  task automatic get_observed_transfers(
      output apb_transfer_observation_t observed_transfer_queue[$]);
    observed_transfer_queue = transfer_queue;
  endtask

  function automatic logic saw_request_phase();
    return request_phase_seen;
  endfunction

  task automatic run();
    fork
      monitor_transfers();
      monitor_protocol();
    join
  endtask
endmodule : br_amba_apb_monitor
