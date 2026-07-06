// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_axil_sim_pkg::*;
import br_amba_sim_pkg::*;

`include "br_amba_sim_macros.svh"

// AXI-Lite request-channel payload monitor.
//
// This monitor observes AW/W/AR handshakes, compares each sampled payload against queued expected
// transactions, and leaves all ready/valid driving to separate bus functional models.
module br_amba_axil_request_monitor #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int AWUserWidth = 2,
    parameter int WUserWidth = 2,
    parameter int ARUserWidth = 2,
    parameter int TimeoutCycles = 100,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic [AddrWidth-1:0] axil_awaddr,
    input logic [AxiProtWidth-1:0] axil_awprot,
    input logic [AWUserWidth-1:0] axil_awuser,
    input logic axil_awvalid,
    input logic axil_awready,
    input logic [DataWidth-1:0] axil_wdata,
    input logic [StrobeWidth-1:0] axil_wstrb,
    input logic [WUserWidth-1:0] axil_wuser,
    input logic axil_wvalid,
    input logic axil_wready,
    input logic [AddrWidth-1:0] axil_araddr,
    input logic [AxiProtWidth-1:0] axil_arprot,
    input logic [ARUserWidth-1:0] axil_aruser,
    input logic axil_arvalid,
    input logic axil_arready,

    output logic failed
);

  axil_aw_t aw_queue[$];
  axil_w_t w_queue[$];
  axil_ar_t ar_queue[$];
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
    input axil_araddr;
    input axil_arprot;
    input axil_aruser;
    input axil_arvalid;
    input axil_arready;
  endclocking

  always @(posedge clk) begin
    ->posedge_clk;
  end

  task automatic init_idle();
    failed = 1'b0;
    aw_queue.delete();
    w_queue.delete();
    ar_queue.delete();
  endtask

  function automatic logic [AddrWidth-1:0] predict_axi2axil_addr(
      input logic [AxiAddrWidth-1:0] start_addr, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstTypeWidth-1:0] burst,
      input int unsigned beat);
    logic [AddrWidth-1:0] incr_addr;
    logic [AddrWidth-1:0] align_mask;
    logic [AddrWidth-1:0] base_addr;
    logic [AddrWidth-1:0] wrap_mask;

    incr_addr = AddrWidth'(start_addr) + (AddrWidth'(beat) << size);
    unique case (axi_burst_type_t'(burst))
      AxiBurstFixed: predict_axi2axil_addr = AddrWidth'(start_addr);
      AxiBurstIncr: begin
        align_mask = {AddrWidth{1'b1}} << size;
        predict_axi2axil_addr = (beat == 0) ? AddrWidth'(start_addr) : (incr_addr & align_mask);
      end
      AxiBurstWrap: begin
        wrap_mask = ((AddrWidth'(len) + 1'b1) << size) - 1'b1;
        base_addr = AddrWidth'(start_addr) & ~wrap_mask;
        predict_axi2axil_addr = base_addr | (incr_addr & wrap_mask);
      end
      default: predict_axi2axil_addr = AddrWidth'(start_addr);
    endcase
  endfunction

  function automatic string channel_name(input axil_request_channel_t channel);
    case (channel)
      AxilRequestAw: channel_name = "AW";
      AxilRequestW:  channel_name = "W";
      AxilRequestAr: channel_name = "AR";
      default:       channel_name = "unknown";
    endcase
  endfunction

  task automatic monitor_aw(input int num_transactions);
    axil_aw_t expected;
    int observed;

    observed = 0;
    while (observed < num_transactions) begin
      @cb;
      if (cb.axil_awvalid && cb.axil_awready) begin
        `BR_AMBA_SIM_CHECK_EQ(aw_queue.size() > 0, 1'b1, "AXI-Lite AW expected queue empty",
                              failed);
        if (aw_queue.size() > 0) begin
          expected = aw_queue.pop_front();
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_awaddr, AddrWidth'(expected.addr),
                                "AXI-Lite AW address mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_awprot, expected.prot, "AXI-Lite AW prot mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_awuser, AWUserWidth'(expected.user),
                                "AXI-Lite AW user mismatch", failed);
        end
        observed++;
      end
    end
  endtask

  task automatic monitor_w(input int num_transactions);
    axil_w_t expected;
    int observed;

    observed = 0;
    while (observed < num_transactions) begin
      @cb;
      if (cb.axil_wvalid && cb.axil_wready) begin
        `BR_AMBA_SIM_CHECK_EQ(w_queue.size() > 0, 1'b1, "AXI-Lite W expected queue empty", failed);
        if (w_queue.size() > 0) begin
          expected = w_queue.pop_front();
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_wdata, DataWidth'(expected.data),
                                "AXI-Lite W data mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_wstrb, StrobeWidth'(expected.strb),
                                "AXI-Lite W strobe mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_wuser, WUserWidth'(expected.user),
                                "AXI-Lite W user mismatch", failed);
        end
        observed++;
      end
    end
  endtask

  task automatic monitor_ar(input int num_transactions);
    axil_ar_t expected;
    int observed;

    observed = 0;
    while (observed < num_transactions) begin
      @cb;
      if (cb.axil_arvalid && cb.axil_arready) begin
        `BR_AMBA_SIM_CHECK_EQ(ar_queue.size() > 0, 1'b1, "AXI-Lite AR expected queue empty",
                              failed);
        if (ar_queue.size() > 0) begin
          expected = ar_queue.pop_front();
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_araddr, AddrWidth'(expected.addr),
                                "AXI-Lite AR address mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_arprot, expected.prot, "AXI-Lite AR prot mismatch", failed);
          `BR_AMBA_SIM_CHECK_EQ(cb.axil_aruser, ARUserWidth'(expected.user),
                                "AXI-Lite AR user mismatch", failed);
        end
        observed++;
      end
    end
  endtask

  task automatic monitor_channel(input axil_request_channel_t channel, input int num_transactions);
    fork
      case (channel)
        AxilRequestAw: monitor_aw(num_transactions);
        AxilRequestW: monitor_w(num_transactions);
        AxilRequestAr: monitor_ar(num_transactions);
        default: report_error("Unknown AXI-Lite request channel", failed);
      endcase
      timeout(posedge_clk, TimeoutCycles * (num_transactions + 1), {
              "Timeout waiting for AXI-Lite ", channel_name(channel), " transfers"}, failed);
    join_any
    disable fork;
  endtask

  task automatic run(input int num_writes, input int num_reads);
    fork
      monitor_channel(AxilRequestAw, num_writes);
      monitor_channel(AxilRequestW, num_writes);
      monitor_channel(AxilRequestAr, num_reads);
    join

    `BR_AMBA_SIM_CHECK_EQ(aw_queue.size(), 0, "AXI-Lite AW expected queue not empty", failed);
    `BR_AMBA_SIM_CHECK_EQ(w_queue.size(), 0, "AXI-Lite W expected queue not empty", failed);
    `BR_AMBA_SIM_CHECK_EQ(ar_queue.size(), 0, "AXI-Lite AR expected queue not empty", failed);
  endtask

endmodule : br_amba_axil_request_monitor
