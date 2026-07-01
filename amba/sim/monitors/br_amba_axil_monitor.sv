// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;

// AXI4-Lite protocol monitor skeleton.
//
// This monitor samples all AXI4-Lite channels according to ready/valid and records
// packaged observations. It does not compare expected behavior.
module br_amba_axil_monitor #(
    parameter  int AddrWidth   = 12,
    parameter  int DataWidth   = 32,
    parameter  int AWUserWidth = 1,
    parameter  int WUserWidth  = 1,
    parameter  int BUserWidth  = 1,
    parameter  int ARUserWidth = 1,
    parameter  int RUserWidth  = 1,
    localparam int StrbWidth   = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic [AddrWidth-1:0] axil_awaddr,
    input logic [AxiProtWidth-1:0] axil_awprot,
    input logic [AWUserWidth-1:0] axil_awuser,
    input logic axil_awvalid,
    input logic axil_awready,
    input logic [DataWidth-1:0] axil_wdata,
    input logic [StrbWidth-1:0] axil_wstrb,
    input logic [WUserWidth-1:0] axil_wuser,
    input logic axil_wvalid,
    input logic axil_wready,
    input logic [AxiRespWidth-1:0] axil_bresp,
    input logic [BUserWidth-1:0] axil_buser,
    input logic axil_bvalid,
    input logic axil_bready,
    input logic [AddrWidth-1:0] axil_araddr,
    input logic [AxiProtWidth-1:0] axil_arprot,
    input logic [ARUserWidth-1:0] axil_aruser,
    input logic axil_arvalid,
    input logic axil_arready,
    input logic [DataWidth-1:0] axil_rdata,
    input logic [AxiRespWidth-1:0] axil_rresp,
    input logic [RUserWidth-1:0] axil_ruser,
    input logic axil_rvalid,
    input logic axil_rready,

    output logic failed
);

  axil_aw_t aw_queue[$];
  axil_w_t w_queue[$];
  axil_b_t b_queue[$];
  axil_ar_t ar_queue[$];
  axil_r_t r_queue[$];
  axil_transaction_kind_t transaction_order_queue[$];
  event posedge_clk;

  clocking cb @(posedge clk);
    default input #1step;
    input axil_awaddr;
    input axil_awprot;
    input axil_awuser;
    input axil_awvalid;
    input axil_awready;
    input axil_wdata;
    input axil_wstrb;
    input axil_wuser;
    input axil_wvalid;
    input axil_wready;
    input axil_bresp;
    input axil_buser;
    input axil_bvalid;
    input axil_bready;
    input axil_araddr;
    input axil_arprot;
    input axil_aruser;
    input axil_arvalid;
    input axil_arready;
    input axil_rdata;
    input axil_rresp;
    input axil_ruser;
    input axil_rvalid;
    input axil_rready;
  endclocking

  always @(posedge clk) begin
    ->posedge_clk;
  end

  task automatic init_idle();
    failed = 1'b0;
    aw_queue.delete();
    w_queue.delete();
    b_queue.delete();
    ar_queue.delete();
    r_queue.delete();
    transaction_order_queue.delete();
  endtask

  task automatic monitor_aw_channel();
    axil_aw_t aw;

    forever begin
      @cb;
      if (cb.axil_awvalid && cb.axil_awready) begin
        aw.addr = AxilAddrWidth'(cb.axil_awaddr);
        aw.prot = cb.axil_awprot;
        aw.user = AxilUserWidth'(cb.axil_awuser);
        aw_queue.push_back(aw);
      end
    end
  endtask

  task automatic monitor_w_channel();
    axil_w_t w;

    forever begin
      @cb;
      if (cb.axil_wvalid && cb.axil_wready) begin
        w.data = AxilDataWidth'(cb.axil_wdata);
        w.strb = AxilStrobeWidth'(cb.axil_wstrb);
        w.user = AxilUserWidth'(cb.axil_wuser);
        w_queue.push_back(w);
      end
    end
  endtask

  task automatic monitor_b_channel();
    axil_b_t b;

    forever begin
      @cb;
      if (cb.axil_bvalid && cb.axil_bready) begin
        b.resp = cb.axil_bresp;
        b.user = AxilUserWidth'(cb.axil_buser);
        b_queue.push_back(b);
      end
    end
  endtask

  task automatic monitor_ar_channel();
    axil_ar_t ar;

    forever begin
      @cb;
      if (cb.axil_arvalid && cb.axil_arready) begin
        ar.addr = AxilAddrWidth'(cb.axil_araddr);
        ar.prot = cb.axil_arprot;
        ar.user = AxilUserWidth'(cb.axil_aruser);
        ar_queue.push_back(ar);
      end
    end
  endtask

  task automatic monitor_r_channel();
    axil_r_t r;

    forever begin
      @cb;
      if (cb.axil_rvalid && cb.axil_rready) begin
        r.data = AxilDataWidth'(cb.axil_rdata);
        r.resp = cb.axil_rresp;
        r.user = AxilUserWidth'(cb.axil_ruser);
        r_queue.push_back(r);
      end
    end
  endtask

  // Record the order of complete AXI-Lite transactions. A write is complete once
  // both AW and W have handshaken; a read is complete on AR handshake.
  task automatic monitor_transaction_order();
    int pending_aw = 0;
    int pending_w = 0;

    forever begin
      @cb;
      if (cb.axil_awvalid && cb.axil_awready) begin
        if (pending_w != 0) begin
          pending_w--;
          transaction_order_queue.push_back(AxilTransactionWrite);
        end else begin
          pending_aw++;
        end
      end
      if (cb.axil_wvalid && cb.axil_wready) begin
        if (pending_aw != 0) begin
          pending_aw--;
          transaction_order_queue.push_back(AxilTransactionWrite);
        end else begin
          pending_w++;
        end
      end
      if (cb.axil_arvalid && cb.axil_arready) begin
        transaction_order_queue.push_back(AxilTransactionRead);
      end
    end
  endtask

  task automatic get_observed_channels(
      output axil_aw_t observed_aw_queue[$], output axil_w_t observed_w_queue[$],
      output axil_b_t observed_b_queue[$], output axil_ar_t observed_ar_queue[$],
      output axil_r_t observed_r_queue[$]);
    observed_aw_queue = aw_queue;
    observed_w_queue  = w_queue;
    observed_b_queue  = b_queue;
    observed_ar_queue = ar_queue;
    observed_r_queue  = r_queue;
  endtask

  task automatic get_observed_transaction_order(
      output axil_transaction_kind_t observed_transaction_order_queue[$]);
    observed_transaction_order_queue = transaction_order_queue;
  endtask

  task automatic run();
    fork
      monitor_aw_channel();
      monitor_w_channel();
      monitor_b_channel();
      monitor_ar_channel();
      monitor_r_channel();
      monitor_transaction_order();
    join
  endtask
endmodule : br_amba_axil_monitor
