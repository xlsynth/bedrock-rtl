// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_amba_sim_macros.svh"

// AXI-Lite target-side Bus Functional Model.
//
// The driver owns only AXI-Lite target inputs: AWREADY, WREADY, B payload/valid, ARREADY, and R
// payload/valid. It accepts request channels and returns queued responses. Payload checking belongs
// in monitors or scoreboards.
module br_amba_axil_target_driver #(
    parameter int DataWidth = 32,
    parameter int BUserWidth = 2,
    parameter int RUserWidth = 2,
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic rst,

    input logic axil_awvalid,
    output logic axil_awready,
    input logic axil_wvalid,
    output logic axil_wready,
    output logic [AxiRespWidth-1:0] axil_bresp,
    output logic [BUserWidth-1:0] axil_buser,
    output logic axil_bvalid,
    input logic axil_bready,
    input logic axil_arvalid,
    output logic axil_arready,
    output logic [DataWidth-1:0] axil_rdata,
    output logic [AxiRespWidth-1:0] axil_rresp,
    output logic [RUserWidth-1:0] axil_ruser,
    output logic axil_rvalid,
    input logic axil_rready,

    output logic failed
);

  axil_b_t b_queue[$];
  axil_r_t r_queue[$];
  int unsigned accepted_aw_count;
  int unsigned accepted_w_count;
  int unsigned accepted_ar_count;
  event posedge_clk;

  clocking cb @(posedge clk);
    default input #1step;
    input axil_awvalid;
    input axil_awready;
    input axil_wvalid;
    input axil_wready;
    input axil_bvalid;
    input axil_bready;
    input axil_arvalid;
    input axil_arready;
    input axil_rvalid;
    input axil_rready;
  endclocking

  always @(posedge clk) begin
    ->posedge_clk;
  end

  task automatic init_idle();
    failed       = 1'b0;
    axil_awready = 1'b0;
    axil_wready  = 1'b0;
    axil_bresp   = '0;
    axil_buser   = '0;
    axil_bvalid  = 1'b0;
    axil_arready = 1'b0;
    axil_rdata   = '0;
    axil_rresp   = '0;
    axil_ruser   = '0;
    axil_rvalid  = 1'b0;
    b_queue.delete();
    r_queue.delete();
    accepted_aw_count = 0;
    accepted_w_count  = 0;
    accepted_ar_count = 0;
  endtask

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  task automatic wait_aw_handshake();
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!(cb.axil_awvalid && cb.axil_awready) && timeout >= 0);
    `BR_AMBA_SIM_CHECK_EQ(cb.axil_awvalid && cb.axil_awready, 1'b1,
                          "Timeout waiting for AXI-Lite AW handshake", failed);
  endtask

  task automatic wait_w_handshake();
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!(cb.axil_wvalid && cb.axil_wready) && timeout >= 0);
    `BR_AMBA_SIM_CHECK_EQ(cb.axil_wvalid && cb.axil_wready, 1'b1,
                          "Timeout waiting for AXI-Lite W handshake", failed);
  endtask

  task automatic wait_b_handshake();
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!(cb.axil_bvalid && cb.axil_bready) && timeout >= 0);
    `BR_AMBA_SIM_CHECK_EQ(cb.axil_bvalid && cb.axil_bready, 1'b1,
                          "Timeout waiting for AXI-Lite B handshake", failed);
  endtask

  task automatic wait_ar_handshake();
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!(cb.axil_arvalid && cb.axil_arready) && timeout >= 0);
    `BR_AMBA_SIM_CHECK_EQ(cb.axil_arvalid && cb.axil_arready, 1'b1,
                          "Timeout waiting for AXI-Lite AR handshake", failed);
  endtask

  task automatic wait_r_handshake();
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!(cb.axil_rvalid && cb.axil_rready) && timeout >= 0);
    `BR_AMBA_SIM_CHECK_EQ(cb.axil_rvalid && cb.axil_rready, 1'b1,
                          "Timeout waiting for AXI-Lite R handshake", failed);
  endtask

  task automatic queue_b_response(input axil_b_t b);
    b_queue.push_back(b);
  endtask

  task automatic queue_r_response(input axil_r_t r);
    r_queue.push_back(r);
  endtask

  function automatic int get_channel_stall_cycles(input int channel_max_stall_cycles,
                                                  input int default_max_stall_cycles);
    int max_stall_cycles;

    max_stall_cycles = (channel_max_stall_cycles >= 0) ? channel_max_stall_cycles :
        default_max_stall_cycles;
    return get_random_stall_cycles(max_stall_cycles);
  endfunction

  task automatic accept_aw(input int stall_cycles);
    if (stall_cycles > 0) begin
      axil_awready = 1'b0;
      wait_cycles(stall_cycles);
    end
    axil_awready = 1'b1;
    wait_aw_handshake();
    accepted_aw_count++;
  endtask

  task automatic accept_w(input int stall_cycles);
    if (stall_cycles > 0) begin
      axil_wready = 1'b0;
      wait_cycles(stall_cycles);
    end
    axil_wready = 1'b1;
    wait_w_handshake();
    accepted_w_count++;
  endtask

  task automatic accept_ar(input int stall_cycles);
    if (stall_cycles > 0) begin
      axil_arready = 1'b0;
      wait_cycles(stall_cycles);
    end
    axil_arready = 1'b1;
    wait_ar_handshake();
    accepted_ar_count++;
  endtask

  task automatic wait_write_request_accepted(input int unsigned request_index);
    fork
      while (!(accepted_aw_count > request_index && accepted_w_count > request_index)) @posedge_clk;
      timeout(posedge_clk, TimeoutCycles, "Timeout waiting for AXI-Lite write request", failed);
    join_any
    disable fork;

    `BR_AMBA_SIM_CHECK_EQ(accepted_aw_count > request_index && accepted_w_count > request_index,
                          1'b1, "Timeout waiting for AXI-Lite write request", failed);
  endtask

  task automatic wait_read_request_accepted(input int unsigned request_index);
    fork
      while (!(accepted_ar_count > request_index)) @posedge_clk;
      timeout(posedge_clk, TimeoutCycles, "Timeout waiting for AXI-Lite read request", failed);
    join_any
    disable fork;

    `BR_AMBA_SIM_CHECK_EQ(accepted_ar_count > request_index, 1'b1,
                          "Timeout waiting for AXI-Lite read request", failed);
  endtask

  task automatic drive_next_b(input int stall_cycles);
    axil_b_t b;

    wait_cycles(stall_cycles);
    `BR_AMBA_SIM_CHECK_EQ(b_queue.size() > 0, 1'b1, "AXI-Lite B response queue empty", failed);
    if (b_queue.size() > 0) begin
      b = b_queue.pop_front();
    end else begin
      b = '0;
    end

    @(negedge clk);
    axil_bresp  = b.resp;
    axil_buser  = BUserWidth'(b.user);
    axil_bvalid = 1'b1;
    wait_b_handshake();
    @(negedge clk);
    axil_bvalid = 1'b0;
    axil_bresp  = '0;
    axil_buser  = '0;
  endtask

  task automatic drive_next_r(input int stall_cycles);
    axil_r_t r;

    wait_cycles(stall_cycles);
    `BR_AMBA_SIM_CHECK_EQ(r_queue.size() > 0, 1'b1, "AXI-Lite R response queue empty", failed);
    if (r_queue.size() > 0) begin
      r = r_queue.pop_front();
    end else begin
      r = '0;
    end

    @(negedge clk);
    axil_rdata  = DataWidth'(r.data);
    axil_rresp  = r.resp;
    axil_ruser  = RUserWidth'(r.user);
    axil_rvalid = 1'b1;
    wait_r_handshake();
    @(negedge clk);
    axil_rvalid = 1'b0;
    axil_rdata  = '0;
    axil_rresp  = '0;
    axil_ruser  = '0;
  endtask

  task automatic run(input int num_write_requests, input int num_read_requests,
                     input int max_stall_cycles, input int awready_max_stall_cycles = -1,
                     input int wready_max_stall_cycles = -1, input int bvalid_max_stall_cycles = -1,
                     input int arready_max_stall_cycles = -1,
                     input int rvalid_max_stall_cycles = -1);
    wait_cycles();

    fork
      begin
        for (int i = 0; i < num_write_requests; i++) begin
          accept_aw(get_channel_stall_cycles(awready_max_stall_cycles, max_stall_cycles));
        end
      end
      begin
        for (int i = 0; i < num_write_requests; i++) begin
          accept_w(get_channel_stall_cycles(wready_max_stall_cycles, max_stall_cycles));
        end
      end
      begin
        for (int i = 0; i < num_write_requests; i++) begin
          wait_write_request_accepted(i);
          drive_next_b(get_channel_stall_cycles(bvalid_max_stall_cycles, max_stall_cycles));
        end
      end
      begin
        for (int i = 0; i < num_read_requests; i++) begin
          accept_ar(get_channel_stall_cycles(arready_max_stall_cycles, max_stall_cycles));
        end
      end
      begin
        for (int i = 0; i < num_read_requests; i++) begin
          wait_read_request_accepted(i);
          drive_next_r(get_channel_stall_cycles(rvalid_max_stall_cycles, max_stall_cycles));
        end
      end
    join

    `BR_AMBA_SIM_CHECK_EQ(b_queue.size(), 0, "AXI-Lite B response queue not empty", failed);
    `BR_AMBA_SIM_CHECK_EQ(r_queue.size(), 0, "AXI-Lite R response queue not empty", failed);
  endtask

endmodule : br_amba_axil_target_driver
