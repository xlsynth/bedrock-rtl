// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_amba_sim_macros.svh"

// AXI response-channel payload monitor.
//
// This monitor observes B/R handshakes, compares each sampled payload against queued expected
// transactions, and leaves BREADY/RREADY driving to a separate bus functional model.
module br_amba_axi_response_monitor #(
    parameter int DataWidth = 32,
    parameter int IdWidth = 3,
    parameter int BUserWidth = 2,
    parameter int RUserWidth = 2,
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic rst,

    input logic [IdWidth-1:0] axi_bid,
    input logic [BUserWidth-1:0] axi_buser,
    input logic [AxiRespWidth-1:0] axi_bresp,
    input logic axi_bvalid,
    input logic axi_bready,
    input logic [IdWidth-1:0] axi_rid,
    input logic [DataWidth-1:0] axi_rdata,
    input logic [RUserWidth-1:0] axi_ruser,
    input logic [AxiRespWidth-1:0] axi_rresp,
    input logic axi_rlast,
    input logic axi_rvalid,
    input logic axi_rready,

    output logic failed
);

  axi_b_t b_queue[$];
  axi_r_t r_queue[$];
  event posedge_clk;

  clocking cb @(posedge clk);
    default input #1step;
    input axi_bid;
    input axi_buser;
    input axi_bresp;
    input axi_bvalid;
    input axi_bready;
    input axi_rid;
    input axi_rdata;
    input axi_ruser;
    input axi_rresp;
    input axi_rlast;
    input axi_rvalid;
    input axi_rready;
  endclocking

  always @(posedge clk) begin
    ->posedge_clk;
  end

  task automatic init_idle();
    failed = 1'b0;
    b_queue.delete();
    r_queue.delete();
  endtask

  function automatic logic [AxiRespWidth-1:0] predict_axi_write_resp(
      input int unsigned beats, input logic [AxiRespWidth-1:0] first_resp,
      input logic [AxiRespWidth-1:0] later_resp);
    if (beats == 0) begin
      predict_axi_write_resp = AxiRespOkay;
    end else if (first_resp != AxiRespOkay || beats == 1) begin
      predict_axi_write_resp = first_resp;
    end else begin
      predict_axi_write_resp = later_resp;
    end
  endfunction

  task automatic monitor_b(input int num_transactions);
    axi_b_t expected;
    int observed;

    observed = 0;
    while (observed < num_transactions) begin
      @cb;
      if (cb.axi_bvalid && cb.axi_bready) begin
        `BR_AMBA_SIM_CHECK_EQ(b_queue.size() > 0, 1'b1, "AXI B expected queue empty", failed);
        if (b_queue.size() > 0) begin
          expected = b_queue.pop_front();
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_bid, IdWidth'(expected.id), "AXI B id mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_bresp, expected.resp, "AXI B resp mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_buser, BUserWidth'(expected.user), "AXI B user mismatch",
                                failed);
        end
        observed++;
      end
    end
  endtask

  task automatic monitor_r(input int num_transactions);
    axi_r_t expected;
    int observed;

    observed = 0;
    while (observed < num_transactions) begin
      @cb;
      if (cb.axi_rvalid && cb.axi_rready) begin
        `BR_AMBA_SIM_CHECK_EQ(r_queue.size() > 0, 1'b1, "AXI R expected queue empty", failed);
        if (r_queue.size() > 0) begin
          expected = r_queue.pop_front();
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_rid, IdWidth'(expected.id), "AXI R id mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_rdata, DataWidth'(expected.data), "AXI R data mismatch",
                                failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_rresp, expected.resp, "AXI R resp mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_ruser, RUserWidth'(expected.user), "AXI R user mismatch",
                                failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axi_rlast, expected.last, "AXI R last mismatch", failed);
        end
        observed++;
      end
    end
  endtask

  task automatic monitor_b_channel(input int num_transactions);
    fork
      monitor_b(num_transactions);
      timeout(posedge_clk, TimeoutCycles * (num_transactions + 1),
              "Timeout waiting for AXI B transfers", failed);
    join_any
    disable fork;
  endtask

  task automatic monitor_r_channel(input int num_transactions);
    fork
      monitor_r(num_transactions);
      timeout(posedge_clk, TimeoutCycles * (num_transactions + 1),
              "Timeout waiting for AXI R transfers", failed);
    join_any
    disable fork;
  endtask

  task automatic run(input int num_writes, input int num_reads);
    fork
      monitor_b_channel(num_writes);
      monitor_r_channel(num_reads);
    join

    `BR_AMBA_SIM_CHECK_EQ(b_queue.size(), 0, "AXI B expected queue not empty", failed);
    `BR_AMBA_SIM_CHECK_EQ(r_queue.size(), 0, "AXI R expected queue not empty", failed);
  endtask

endmodule : br_amba_axi_response_monitor
