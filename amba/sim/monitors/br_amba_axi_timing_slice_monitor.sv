// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;

// AXI timing-slice payload monitor.
//
// This is not a generic AXI protocol monitor. It is specific to
// br_amba_axi_timing_slice and checks that every accepted input payload on each
// independent channel appears unchanged and in order on that channel's output.
module br_amba_axi_timing_slice_monitor #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 2,
    parameter int AWUserWidth = 2,
    parameter int WUserWidth = 2,
    parameter int ARUserWidth = 2,
    parameter int BUserWidth = 2,
    parameter int RUserWidth = 2,
    parameter int TimeoutCycles = 100,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    input logic [AddrWidth-1:0] target_awaddr,
    input logic [IdWidth-1:0] target_awid,
    input logic [AxiBurstLenWidth-1:0] target_awlen,
    input logic [AxiBurstSizeWidth-1:0] target_awsize,
    input logic [AxiBurstTypeWidth-1:0] target_awburst,
    input logic [AxiProtWidth-1:0] target_awprot,
    input logic [AWUserWidth-1:0] target_awuser,
    input logic target_awvalid,
    input logic target_awready,
    input logic [DataWidth-1:0] target_wdata,
    input logic [StrobeWidth-1:0] target_wstrb,
    input logic [WUserWidth-1:0] target_wuser,
    input logic target_wlast,
    input logic target_wvalid,
    input logic target_wready,
    input logic [IdWidth-1:0] target_bid,
    input logic [BUserWidth-1:0] target_buser,
    input logic [AxiRespWidth-1:0] target_bresp,
    input logic target_bvalid,
    input logic target_bready,
    input logic [AddrWidth-1:0] target_araddr,
    input logic [IdWidth-1:0] target_arid,
    input logic [AxiBurstLenWidth-1:0] target_arlen,
    input logic [AxiBurstSizeWidth-1:0] target_arsize,
    input logic [AxiBurstTypeWidth-1:0] target_arburst,
    input logic [AxiProtWidth-1:0] target_arprot,
    input logic [ARUserWidth-1:0] target_aruser,
    input logic target_arvalid,
    input logic target_arready,
    input logic [IdWidth-1:0] target_rid,
    input logic [DataWidth-1:0] target_rdata,
    input logic [RUserWidth-1:0] target_ruser,
    input logic [AxiRespWidth-1:0] target_rresp,
    input logic target_rlast,
    input logic target_rvalid,
    input logic target_rready,

    input logic [AddrWidth-1:0] init_awaddr,
    input logic [IdWidth-1:0] init_awid,
    input logic [AxiBurstLenWidth-1:0] init_awlen,
    input logic [AxiBurstSizeWidth-1:0] init_awsize,
    input logic [AxiBurstTypeWidth-1:0] init_awburst,
    input logic [AxiProtWidth-1:0] init_awprot,
    input logic [AWUserWidth-1:0] init_awuser,
    input logic init_awvalid,
    input logic init_awready,
    input logic [DataWidth-1:0] init_wdata,
    input logic [StrobeWidth-1:0] init_wstrb,
    input logic [WUserWidth-1:0] init_wuser,
    input logic init_wlast,
    input logic init_wvalid,
    input logic init_wready,
    input logic [IdWidth-1:0] init_bid,
    input logic [BUserWidth-1:0] init_buser,
    input logic [AxiRespWidth-1:0] init_bresp,
    input logic init_bvalid,
    input logic init_bready,
    input logic [AddrWidth-1:0] init_araddr,
    input logic [IdWidth-1:0] init_arid,
    input logic [AxiBurstLenWidth-1:0] init_arlen,
    input logic [AxiBurstSizeWidth-1:0] init_arsize,
    input logic [AxiBurstTypeWidth-1:0] init_arburst,
    input logic [AxiProtWidth-1:0] init_arprot,
    input logic [ARUserWidth-1:0] init_aruser,
    input logic init_arvalid,
    input logic init_arready,
    input logic [IdWidth-1:0] init_rid,
    input logic [DataWidth-1:0] init_rdata,
    input logic [RUserWidth-1:0] init_ruser,
    input logic [AxiRespWidth-1:0] init_rresp,
    input logic init_rlast,
    input logic init_rvalid,
    input logic init_rready,

    output logic failed
);

  typedef enum int {
    ChannelAw,
    ChannelW,
    ChannelAr,
    ChannelB,
    ChannelR
  } axi_channel_e;

  localparam int AwPayloadWidth = $bits(axi_aw_t);
  localparam int WPayloadWidth = $bits(axi_w_t);
  localparam int ArPayloadWidth = $bits(axi_ar_t);
  localparam int BPayloadWidth = $bits(axi_b_t);
  localparam int RPayloadWidth = $bits(axi_r_t);
  localparam int MaxAddrPayloadWidth =
      (AwPayloadWidth > ArPayloadWidth) ? AwPayloadWidth : ArPayloadWidth;
  localparam int MaxDataPayloadWidth =
      (WPayloadWidth > RPayloadWidth) ? WPayloadWidth : RPayloadWidth;
  localparam int MaxRespPayloadWidth =
      (BPayloadWidth > MaxDataPayloadWidth) ? BPayloadWidth : MaxDataPayloadWidth;
  localparam int MaxPayloadWidth =
      (MaxAddrPayloadWidth > MaxRespPayloadWidth) ? MaxAddrPayloadWidth : MaxRespPayloadWidth;

  task automatic init_idle();
    failed = 1'b0;
  endtask

  task automatic check(input logic condition, input string message);
    if (!condition) begin
      failed = 1'b1;
      $error("%s", message);
    end
  endtask

  task automatic check_valids_idle();
    check(!target_awvalid, "target_awvalid asserted after monitor run");
    check(!target_wvalid, "target_wvalid asserted after monitor run");
    check(!target_arvalid, "target_arvalid asserted after monitor run");
    check(!init_bvalid, "init_bvalid asserted after monitor run");
    check(!init_rvalid, "init_rvalid asserted after monitor run");
    check(!init_awvalid, "init_awvalid asserted after monitor run");
    check(!init_wvalid, "init_wvalid asserted after monitor run");
    check(!target_bvalid, "target_bvalid asserted after monitor run");
    check(!init_arvalid, "init_arvalid asserted after monitor run");
    check(!target_rvalid, "target_rvalid asserted after monitor run");
  endtask

  function automatic axi_aw_t get_target_aw();
    get_target_aw.addr  = target_awaddr;
    get_target_aw.id    = target_awid;
    get_target_aw.len   = target_awlen;
    get_target_aw.size  = target_awsize;
    get_target_aw.burst = target_awburst;
    get_target_aw.prot  = target_awprot;
    get_target_aw.user  = target_awuser;
  endfunction

  function automatic axi_aw_t get_init_aw();
    get_init_aw.addr  = init_awaddr;
    get_init_aw.id    = init_awid;
    get_init_aw.len   = init_awlen;
    get_init_aw.size  = init_awsize;
    get_init_aw.burst = init_awburst;
    get_init_aw.prot  = init_awprot;
    get_init_aw.user  = init_awuser;
  endfunction

  function automatic axi_w_t get_target_w();
    get_target_w.data = target_wdata;
    get_target_w.strb = target_wstrb;
    get_target_w.user = target_wuser;
    get_target_w.last = target_wlast;
  endfunction

  function automatic axi_w_t get_init_w();
    get_init_w.data = init_wdata;
    get_init_w.strb = init_wstrb;
    get_init_w.user = init_wuser;
    get_init_w.last = init_wlast;
  endfunction

  function automatic axi_ar_t get_target_ar();
    get_target_ar.addr  = target_araddr;
    get_target_ar.id    = target_arid;
    get_target_ar.len   = target_arlen;
    get_target_ar.size  = target_arsize;
    get_target_ar.burst = target_arburst;
    get_target_ar.prot  = target_arprot;
    get_target_ar.user  = target_aruser;
  endfunction

  function automatic axi_ar_t get_init_ar();
    get_init_ar.addr  = init_araddr;
    get_init_ar.id    = init_arid;
    get_init_ar.len   = init_arlen;
    get_init_ar.size  = init_arsize;
    get_init_ar.burst = init_arburst;
    get_init_ar.prot  = init_arprot;
    get_init_ar.user  = init_aruser;
  endfunction

  function automatic axi_b_t get_init_b();
    get_init_b.id   = init_bid;
    get_init_b.user = init_buser;
    get_init_b.resp = init_bresp;
  endfunction

  function automatic axi_b_t get_target_b();
    get_target_b.id   = target_bid;
    get_target_b.user = target_buser;
    get_target_b.resp = target_bresp;
  endfunction

  function automatic axi_r_t get_init_r();
    get_init_r.id   = init_rid;
    get_init_r.data = init_rdata;
    get_init_r.resp = init_rresp;
    get_init_r.user = init_ruser;
    get_init_r.last = init_rlast;
  endfunction

  function automatic axi_r_t get_target_r();
    get_target_r.id   = target_rid;
    get_target_r.data = target_rdata;
    get_target_r.resp = target_rresp;
    get_target_r.user = target_ruser;
    get_target_r.last = target_rlast;
  endfunction

  function automatic logic input_handshake(input axi_channel_e channel);
    case (channel)
      ChannelAw: input_handshake = target_awvalid && target_awready;
      ChannelW:  input_handshake = target_wvalid && target_wready;
      ChannelAr: input_handshake = target_arvalid && target_arready;
      ChannelB:  input_handshake = init_bvalid && init_bready;
      ChannelR:  input_handshake = init_rvalid && init_rready;
      default:   input_handshake = 1'b0;
    endcase
  endfunction

  function automatic logic output_handshake(input axi_channel_e channel);
    case (channel)
      ChannelAw: output_handshake = init_awvalid && init_awready;
      ChannelW:  output_handshake = init_wvalid && init_wready;
      ChannelAr: output_handshake = init_arvalid && init_arready;
      ChannelB:  output_handshake = target_bvalid && target_bready;
      ChannelR:  output_handshake = target_rvalid && target_rready;
      default:   output_handshake = 1'b0;
    endcase
  endfunction

  function automatic logic [MaxPayloadWidth-1:0] get_input_payload(input axi_channel_e channel);
    get_input_payload = '0;
    case (channel)
      ChannelAw: get_input_payload[AwPayloadWidth-1:0] = get_target_aw();
      ChannelW:  get_input_payload[WPayloadWidth-1:0] = get_target_w();
      ChannelAr: get_input_payload[ArPayloadWidth-1:0] = get_target_ar();
      ChannelB:  get_input_payload[BPayloadWidth-1:0] = get_init_b();
      ChannelR:  get_input_payload[RPayloadWidth-1:0] = get_init_r();
      default:   get_input_payload = '0;
    endcase
  endfunction

  function automatic logic [MaxPayloadWidth-1:0] get_output_payload(input axi_channel_e channel);
    get_output_payload = '0;
    case (channel)
      ChannelAw: get_output_payload[AwPayloadWidth-1:0] = get_init_aw();
      ChannelW:  get_output_payload[WPayloadWidth-1:0] = get_init_w();
      ChannelAr: get_output_payload[ArPayloadWidth-1:0] = get_init_ar();
      ChannelB:  get_output_payload[BPayloadWidth-1:0] = get_target_b();
      ChannelR:  get_output_payload[RPayloadWidth-1:0] = get_target_r();
      default:   get_output_payload = '0;
    endcase
  endfunction

  task automatic monitor_channel(input axi_channel_e channel, input int num_transactions,
                                 input string channel_name);
    logic [MaxPayloadWidth-1:0] queue[$];
    logic [MaxPayloadWidth-1:0] expected;
    int popped;
    int timeout;

    popped  = 0;
    timeout = TimeoutCycles;
    while (popped < num_transactions && timeout > 0) begin
      @(posedge clk);
      if (rst) begin
        queue.delete();
      end else begin
        if (input_handshake(channel)) begin
          queue.push_back(get_input_payload(channel));
        end
        if (output_handshake(channel)) begin
          check(queue.size() > 0, {channel_name, " output transfer without expected payload"});
          if (queue.size() > 0) begin
            expected = queue.pop_front();
            check(get_output_payload(channel) === expected, {channel_name, " payload mismatch"});
          end
          popped++;
        end
        timeout--;
      end
    end
    check(popped == num_transactions, {"Timeout waiting for ", channel_name, " output transfers"});
    check(queue.size() == 0, {channel_name, " monitor queue not empty"});
  endtask

  task automatic run(input int num_writes, input int num_reads);
    fork
      monitor_channel(ChannelAw, num_writes, "AW");
      monitor_channel(ChannelW, num_writes, "W");
      monitor_channel(ChannelAr, num_reads, "AR");
      monitor_channel(ChannelB, num_writes, "B");
      monitor_channel(ChannelR, num_reads, "R");
    join

    repeat (2) @(posedge clk);
    check_valids_idle();
  endtask

endmodule : br_amba_axi_timing_slice_monitor
