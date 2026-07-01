// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axil_sim_pkg::*;
import br_amba_axil_monitor_sim_pkg::*;

// AXI4-Lite protocol monitor.
//
// This monitor samples all AXI4-Lite channels according to ready/valid,
// records packaged observations, and checks protocol-local rules. DUT-specific
// expected behavior belongs in scoreboards.
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

  axil_aw_observation_t aw_queue[$];
  axil_w_observation_t w_queue[$];
  axil_b_observation_t b_queue[$];
  axil_ar_observation_t ar_queue[$];
  axil_r_observation_t r_queue[$];
  axil_request_state_observation_t request_state_queue[$];
  logic aw_handshake;
  logic w_handshake;
  logic b_handshake;
  logic ar_handshake;
  logic r_handshake;

  clocking cb @(posedge clk);
    default input #1step;
    input rst;
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

  always_comb begin
    aw_handshake = cb.axil_awvalid && cb.axil_awready;
    w_handshake  = cb.axil_wvalid && cb.axil_wready;
    b_handshake  = cb.axil_bvalid && cb.axil_bready;
    ar_handshake = cb.axil_arvalid && cb.axil_arready;
    r_handshake  = cb.axil_rvalid && cb.axil_rready;
  end

  task automatic init_idle();
    failed = 1'b0;
    aw_queue.delete();
    w_queue.delete();
    b_queue.delete();
    ar_queue.delete();
    r_queue.delete();
    request_state_queue.delete();
  endtask

  task automatic monitor_request_state();
    axil_request_state_observation_t request_state;

    forever begin
      @cb;
      if (!cb.rst && (cb.axil_awvalid || cb.axil_awready || cb.axil_wvalid ||
                      cb.axil_wready || cb.axil_arvalid || cb.axil_arready)) begin
        request_state.awvalid   = cb.axil_awvalid;
        request_state.awready   = cb.axil_awready;
        request_state.wvalid    = cb.axil_wvalid;
        request_state.wready    = cb.axil_wready;
        request_state.arvalid   = cb.axil_arvalid;
        request_state.arready   = cb.axil_arready;
        request_state.timestamp = $time;
        request_state_queue.push_back(request_state);
      end
    end
  endtask

  task automatic monitor_aw_channel();
    axil_aw_observation_t aw;

    forever begin
      @cb;
      if (!cb.rst && aw_handshake) begin
        aw.packet.addr = AxilAddrWidth'(cb.axil_awaddr);
        aw.packet.prot = cb.axil_awprot;
        aw.packet.user = AxilUserWidth'(cb.axil_awuser);
        aw.timestamp   = $time;
        aw_queue.push_back(aw);
      end
    end
  endtask

  task automatic monitor_w_channel();
    axil_w_observation_t w;

    forever begin
      @cb;
      if (!cb.rst && w_handshake) begin
        w.packet.data = AxilDataWidth'(cb.axil_wdata);
        w.packet.strb = AxilStrobeWidth'(cb.axil_wstrb);
        w.packet.user = AxilUserWidth'(cb.axil_wuser);
        w.timestamp   = $time;
        w_queue.push_back(w);
      end
    end
  endtask

  task automatic monitor_b_channel();
    axil_b_observation_t b;

    forever begin
      @cb;
      if (!cb.rst && b_handshake) begin
        b.packet.resp = cb.axil_bresp;
        b.packet.user = AxilUserWidth'(cb.axil_buser);
        b.timestamp   = $time;
        b_queue.push_back(b);
      end
    end
  endtask

  task automatic monitor_ar_channel();
    axil_ar_observation_t ar;

    forever begin
      @cb;
      if (!cb.rst && ar_handshake) begin
        ar.packet.addr = AxilAddrWidth'(cb.axil_araddr);
        ar.packet.prot = cb.axil_arprot;
        ar.packet.user = AxilUserWidth'(cb.axil_aruser);
        ar.timestamp   = $time;
        ar_queue.push_back(ar);
      end
    end
  endtask

  task automatic monitor_r_channel();
    axil_r_observation_t r;

    forever begin
      @cb;
      if (!cb.rst && r_handshake) begin
        r.packet.data = AxilDataWidth'(cb.axil_rdata);
        r.packet.resp = cb.axil_rresp;
        r.packet.user = AxilUserWidth'(cb.axil_ruser);
        r.timestamp   = $time;
        r_queue.push_back(r);
      end
    end
  endtask

  task automatic check_aw_wait(input logic aw_wait, input axil_aw_t held_aw);
    if (aw_wait) begin
      if (!cb.axil_awvalid) begin
        failed = 1'b1;
        $error("AXI-Lite AWVALID deasserted before AWREADY");
      end else if (held_aw.addr !== AxilAddrWidth'(cb.axil_awaddr) ||
                   held_aw.prot !== cb.axil_awprot ||
                   held_aw.user !== AxilUserWidth'(cb.axil_awuser)) begin
        failed = 1'b1;
        $error("AXI-Lite AW payload changed while AWVALID was waiting for AWREADY");
      end
    end
  endtask

  task automatic check_w_wait(input logic w_wait, input axil_w_t held_w);
    if (w_wait) begin
      if (!cb.axil_wvalid) begin
        failed = 1'b1;
        $error("AXI-Lite WVALID deasserted before WREADY");
      end else if (held_w.data !== AxilDataWidth'(cb.axil_wdata) ||
                   held_w.strb !== AxilStrobeWidth'(cb.axil_wstrb) ||
                   held_w.user !== AxilUserWidth'(cb.axil_wuser)) begin
        failed = 1'b1;
        $error("AXI-Lite W payload changed while WVALID was waiting for WREADY");
      end
    end
  endtask

  task automatic check_b_wait(input logic b_wait, input axil_b_t held_b);
    if (b_wait) begin
      if (!cb.axil_bvalid) begin
        failed = 1'b1;
        $error("AXI-Lite BVALID deasserted before BREADY");
      end else if (held_b.resp !== cb.axil_bresp ||
                   held_b.user !== AxilUserWidth'(cb.axil_buser)) begin
        failed = 1'b1;
        $error("AXI-Lite B payload changed while BVALID was waiting for BREADY");
      end
    end
  endtask

  task automatic check_ar_wait(input logic ar_wait, input axil_ar_t held_ar);
    if (ar_wait) begin
      if (!cb.axil_arvalid) begin
        failed = 1'b1;
        $error("AXI-Lite ARVALID deasserted before ARREADY");
      end else if (held_ar.addr !== AxilAddrWidth'(cb.axil_araddr) ||
                   held_ar.prot !== cb.axil_arprot ||
                   held_ar.user !== AxilUserWidth'(cb.axil_aruser)) begin
        failed = 1'b1;
        $error("AXI-Lite AR payload changed while ARVALID was waiting for ARREADY");
      end
    end
  endtask

  task automatic check_r_wait(input logic r_wait, input axil_r_t held_r);
    if (r_wait) begin
      if (!cb.axil_rvalid) begin
        failed = 1'b1;
        $error("AXI-Lite RVALID deasserted before RREADY");
      end else if (held_r.data !== AxilDataWidth'(cb.axil_rdata) ||
                   held_r.resp !== cb.axil_rresp ||
                   held_r.user !== AxilUserWidth'(cb.axil_ruser)) begin
        failed = 1'b1;
        $error("AXI-Lite R payload changed while RVALID was waiting for RREADY");
      end
    end
  endtask

  task automatic check_waiting_payloads(
      input logic aw_wait, input logic w_wait, input logic b_wait, input logic ar_wait,
      input logic r_wait, input axil_aw_t held_aw, input axil_w_t held_w, input axil_b_t held_b,
      input axil_ar_t held_ar, input axil_r_t held_r);
    check_aw_wait(aw_wait, held_aw);
    check_w_wait(w_wait, held_w);
    check_b_wait(b_wait, held_b);
    check_ar_wait(ar_wait, held_ar);
    check_r_wait(r_wait, held_r);
  endtask

  task automatic update_pending_counts(ref int unmatched_aw, ref int unmatched_w,
                                       ref int awaiting_b, ref int awaiting_r);
    if (aw_handshake) begin
      if (unmatched_w != 0) begin
        unmatched_w--;
        awaiting_b++;
      end else begin
        unmatched_aw++;
      end
    end
    if (w_handshake) begin
      if (unmatched_aw != 0) begin
        unmatched_aw--;
        awaiting_b++;
      end else begin
        unmatched_w++;
      end
    end
    if (ar_handshake) begin
      awaiting_r++;
    end

    // Apply current-cycle request handshakes before response checks so a
    // zero-latency completer can return B/R valid in the same sampled cycle
    // as the matching request acceptance.
    if (cb.axil_bvalid && awaiting_b == 0) begin
      failed = 1'b1;
      $error("AXI-Lite BVALID asserted before an AW/W write request completed");
    end
    if (cb.axil_rvalid && awaiting_r == 0) begin
      failed = 1'b1;
      $error("AXI-Lite RVALID asserted before an AR read request completed");
    end

    if (b_handshake && awaiting_b != 0) begin
      awaiting_b--;
    end
    if (r_handshake && awaiting_r != 0) begin
      awaiting_r--;
    end
  endtask

  task automatic update_wait_tracking(ref logic aw_wait, ref logic w_wait, ref logic b_wait,
                                      ref logic ar_wait, ref logic r_wait, ref axil_aw_t held_aw,
                                      ref axil_w_t held_w, ref axil_b_t held_b,
                                      ref axil_ar_t held_ar, ref axil_r_t held_r);
    if (aw_handshake || !cb.axil_awvalid) begin
      aw_wait = 1'b0;
    end else if (!aw_wait && cb.axil_awvalid && !cb.axil_awready) begin
      aw_wait = 1'b1;
      held_aw.addr = AxilAddrWidth'(cb.axil_awaddr);
      held_aw.prot = cb.axil_awprot;
      held_aw.user = AxilUserWidth'(cb.axil_awuser);
    end
    if (w_handshake || !cb.axil_wvalid) begin
      w_wait = 1'b0;
    end else if (!w_wait && cb.axil_wvalid && !cb.axil_wready) begin
      w_wait = 1'b1;
      held_w.data = AxilDataWidth'(cb.axil_wdata);
      held_w.strb = AxilStrobeWidth'(cb.axil_wstrb);
      held_w.user = AxilUserWidth'(cb.axil_wuser);
    end
    if (b_handshake || !cb.axil_bvalid) begin
      b_wait = 1'b0;
    end else if (!b_wait && cb.axil_bvalid && !cb.axil_bready) begin
      b_wait = 1'b1;
      held_b.resp = cb.axil_bresp;
      held_b.user = AxilUserWidth'(cb.axil_buser);
    end
    if (ar_handshake || !cb.axil_arvalid) begin
      ar_wait = 1'b0;
    end else if (!ar_wait && cb.axil_arvalid && !cb.axil_arready) begin
      ar_wait = 1'b1;
      held_ar.addr = AxilAddrWidth'(cb.axil_araddr);
      held_ar.prot = cb.axil_arprot;
      held_ar.user = AxilUserWidth'(cb.axil_aruser);
    end
    if (r_handshake || !cb.axil_rvalid) begin
      r_wait = 1'b0;
    end else if (!r_wait && cb.axil_rvalid && !cb.axil_rready) begin
      r_wait = 1'b1;
      held_r.data = AxilDataWidth'(cb.axil_rdata);
      held_r.resp = cb.axil_rresp;
      held_r.user = AxilUserWidth'(cb.axil_ruser);
    end
  endtask

  task automatic reset_protocol_state(ref int unmatched_aw, ref int unmatched_w, ref int awaiting_b,
                                      ref int awaiting_r, ref logic aw_wait, ref logic w_wait,
                                      ref logic b_wait, ref logic ar_wait, ref logic r_wait);
    unmatched_aw = 0;
    unmatched_w = 0;
    awaiting_b = 0;
    awaiting_r = 0;
    aw_wait = 1'b0;
    w_wait = 1'b0;
    b_wait = 1'b0;
    ar_wait = 1'b0;
    r_wait = 1'b0;
  endtask

  // Checks protocol-local AXI-Lite rules from one sampled clock view:
  // - VALID and payload remain stable while waiting for READY;
  // - BVALID is not asserted before matching AW and W handshakes;
  // - RVALID is not asserted before a matching AR handshake.
  task automatic monitor_protocol();
    int unmatched_aw = 0;
    int unmatched_w = 0;
    int awaiting_b = 0;
    int awaiting_r = 0;
    logic aw_wait = 1'b0;
    logic w_wait = 1'b0;
    logic b_wait = 1'b0;
    logic ar_wait = 1'b0;
    logic r_wait = 1'b0;
    axil_aw_t held_aw;
    axil_w_t held_w;
    axil_b_t held_b;
    axil_ar_t held_ar;
    axil_r_t held_r;

    forever begin
      @cb;
      if (cb.rst) begin
        reset_protocol_state(unmatched_aw, unmatched_w, awaiting_b, awaiting_r, aw_wait, w_wait,
                             b_wait, ar_wait, r_wait);
      end else begin
        check_waiting_payloads(aw_wait, w_wait, b_wait, ar_wait, r_wait, held_aw, held_w, held_b,
                               held_ar, held_r);
        update_pending_counts(unmatched_aw, unmatched_w, awaiting_b, awaiting_r);
        update_wait_tracking(aw_wait, w_wait, b_wait, ar_wait, r_wait, held_aw, held_w, held_b,
                             held_ar, held_r);
      end
    end
  endtask

  task automatic get_observed_request_observations(
      output axil_aw_observation_t observed_aw_queue[$],
      output axil_w_observation_t observed_w_queue[$],
      output axil_ar_observation_t observed_ar_queue[$]);
    observed_aw_queue = aw_queue;
    observed_w_queue  = w_queue;
    observed_ar_queue = ar_queue;
  endtask

  task automatic get_observed_response_observations(
      output axil_b_observation_t observed_b_queue[$],
      output axil_r_observation_t observed_r_queue[$]);
    observed_b_queue = b_queue;
    observed_r_queue = r_queue;
  endtask

  task automatic get_observed_request_state_observations(
      output axil_request_state_observation_t observed_request_state_queue[$]);
    observed_request_state_queue = request_state_queue;
  endtask

  task automatic run();
    fork
      monitor_request_state();
      monitor_aw_channel();
      monitor_w_channel();
      monitor_b_channel();
      monitor_ar_channel();
      monitor_r_channel();
      monitor_protocol();
    join
  endtask
endmodule : br_amba_axil_monitor
