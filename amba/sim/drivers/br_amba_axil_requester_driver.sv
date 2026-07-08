// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_sim_pkg::*;
import br_amba_axil_sim_pkg::*;

// AXI4-Lite requester-side driver.
//
// The driver owns only AXI4-Lite requester outputs: AW/W/AR payloads and valids,
// plus BREADY/RREADY. Payload observation and checking belong in monitors and
// scoreboards.
module br_amba_axil_requester_driver #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int TimeoutCycles = 100,
    localparam int StrbWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    output logic [AddrWidth-1:0] axil_awaddr,
    output logic [AxiProtWidth-1:0] axil_awprot,
    output logic axil_awvalid,
    input logic axil_awready,
    output logic [DataWidth-1:0] axil_wdata,
    output logic [StrbWidth-1:0] axil_wstrb,
    output logic axil_wvalid,
    input logic axil_wready,
    input logic axil_bvalid,
    output logic axil_bready,
    output logic [AddrWidth-1:0] axil_araddr,
    output logic [AxiProtWidth-1:0] axil_arprot,
    output logic axil_arvalid,
    input logic axil_arready,
    input logic axil_rvalid,
    output logic axil_rready,

    output logic failed
);

  int bready_stall_queue[$];
  int rready_stall_queue[$];
  axil_aw_driver_item_t aw_queue[$];
  axil_w_driver_item_t w_queue[$];
  axil_ar_driver_item_t ar_queue[$];
  event sample_tick;

  clocking cb @(posedge clk);
    default input #1step;
    input rst;
    input axil_awready;
    input axil_wready;
    input axil_bvalid;
    input axil_arready;
    input axil_rvalid;
    input axil_awvalid;
    input axil_wvalid;
    input axil_bready;
    input axil_arvalid;
    input axil_rready;
  endclocking

  always begin
    @cb;
    ->sample_tick;
  end

  task automatic init_idle();
    axil_awaddr  = '0;
    axil_awprot  = '0;
    axil_awvalid = 1'b0;
    axil_wdata   = '0;
    axil_wstrb   = '0;
    axil_wvalid  = 1'b0;
    axil_bready  = 1'b0;
    axil_araddr  = '0;
    axil_arprot  = '0;
    axil_arvalid = 1'b0;
    axil_rready  = 1'b0;
    failed       = 1'b0;
    bready_stall_queue.delete();
    rready_stall_queue.delete();
    aw_queue.delete();
    w_queue.delete();
    ar_queue.delete();
  endtask

  task automatic fail(input string message);
    failed = 1'b1;
    $error("%s", message);
  endtask

  task automatic queue_write(input logic [AddrWidth-1:0] addr, input logic [AxiProtWidth-1:0] prot,
                             input logic [DataWidth-1:0] data, input logic [StrbWidth-1:0] strb,
                             input int aw_gap_cycles, input int w_gap_cycles,
                             input int b_stall_cycles);
    aw_queue.push_back('{addr: AxilAddrWidth'(addr), prot: prot, gap_cycles: aw_gap_cycles});
    w_queue.push_back('{data: AxilDataWidth'(data), strb: AxilStrobeWidth'(strb),
                      gap_cycles: w_gap_cycles});
    bready_stall_queue.push_back(b_stall_cycles);
  endtask

  task automatic queue_read(input logic [AddrWidth-1:0] addr, input logic [AxiProtWidth-1:0] prot,
                            input int ar_gap_cycles, input int r_stall_cycles);
    ar_queue.push_back('{addr: AxilAddrWidth'(addr), prot: prot, gap_cycles: ar_gap_cycles});
    rready_stall_queue.push_back(r_stall_cycles);
  endtask

  function automatic logic is_handshake_seen(input axil_handshake_channel_t channel);
    unique case (channel)
      AxilHandshakeAw: is_handshake_seen = cb.axil_awvalid && cb.axil_awready;
      AxilHandshakeW:  is_handshake_seen = cb.axil_wvalid && cb.axil_wready;
      AxilHandshakeB:  is_handshake_seen = cb.axil_bvalid && cb.axil_bready;
      AxilHandshakeAr: is_handshake_seen = cb.axil_arvalid && cb.axil_arready;
      AxilHandshakeR:  is_handshake_seen = cb.axil_rvalid && cb.axil_rready;
      default:         is_handshake_seen = 1'b0;
    endcase
  endfunction

  function automatic logic is_valid_seen(input axil_handshake_channel_t channel);
    unique case (channel)
      AxilHandshakeAw: is_valid_seen = cb.axil_awvalid;
      AxilHandshakeW:  is_valid_seen = cb.axil_wvalid;
      AxilHandshakeB:  is_valid_seen = cb.axil_bvalid;
      AxilHandshakeAr: is_valid_seen = cb.axil_arvalid;
      AxilHandshakeR:  is_valid_seen = cb.axil_rvalid;
      default:         is_valid_seen = 1'b0;
    endcase
  endfunction

  task automatic wait_handshake(input axil_handshake_channel_t channel, input string channel_name);
    fork
      do @cb; while (!is_handshake_seen(channel));
      timeout(sample_tick, TimeoutCycles, $sformatf(
              "Timeout waiting for AXI-Lite %s handshake", channel_name), failed);
    join_any
    disable fork;
  endtask

  task automatic wait_valid(input axil_handshake_channel_t channel, input string channel_name);
    fork
      do @cb; while (!is_valid_seen(channel));
      timeout(sample_tick, TimeoutCycles, $sformatf(
              "Timeout waiting for AXI-Lite %s valid", channel_name), failed);
    join_any
    disable fork;
  endtask

  task automatic wait_response_stall(input axil_handshake_channel_t channel,
                                     input string channel_name, input int stall_cycles);
    for (int stall_cycle = 0; stall_cycle < stall_cycles; stall_cycle++) begin
      if (stall_cycle == 0) begin
        wait_valid(channel, channel_name);
        if (failed) begin
          return;
        end
      end
      @(negedge clk);
    end
  endtask

  task automatic drive_aw_channel(input int num_writes);
    axil_aw_driver_item_t item;

    for (int i = 0; i < num_writes; i++) begin
      if (aw_queue.size() == 0) begin
        fail("AXI-Lite requester AW queue underflow");
        return;
      end
      item = aw_queue.pop_front();
      repeat (item.gap_cycles) @(negedge clk);
      axil_awaddr  = AddrWidth'(item.addr);
      axil_awprot  = item.prot;
      axil_awvalid = 1'b1;
      wait_handshake(AxilHandshakeAw, "AW");
      if (failed) begin
        axil_awvalid = 1'b0;
        return;
      end
      @(negedge clk);
      axil_awvalid = 1'b0;
    end
  endtask

  task automatic drive_w_channel(input int num_writes);
    axil_w_driver_item_t item;

    for (int i = 0; i < num_writes; i++) begin
      if (w_queue.size() == 0) begin
        fail("AXI-Lite requester W queue underflow");
        return;
      end
      item = w_queue.pop_front();
      repeat (item.gap_cycles) @(negedge clk);
      axil_wdata  = DataWidth'(item.data);
      axil_wstrb  = StrbWidth'(item.strb);
      axil_wvalid = 1'b1;
      wait_handshake(AxilHandshakeW, "W");
      if (failed) begin
        axil_wvalid = 1'b0;
        return;
      end
      @(negedge clk);
      axil_wvalid = 1'b0;
    end
  endtask

  task automatic drive_b_channel(input int num_writes);
    int stall_cycles;

    for (int i = 0; i < num_writes; i++) begin
      if (bready_stall_queue.size() == 0) begin
        fail("AXI-Lite requester B stall queue underflow");
        return;
      end
      stall_cycles = bready_stall_queue.pop_front();
      wait_response_stall(AxilHandshakeB, "B", stall_cycles);
      if (failed) begin
        return;
      end
      axil_bready = 1'b1;
      wait_handshake(AxilHandshakeB, "B");
      if (failed) begin
        axil_bready = 1'b0;
        return;
      end
      @(negedge clk);
      axil_bready = 1'b0;
    end
  endtask

  task automatic drive_ar_channel(input int num_reads);
    axil_ar_driver_item_t item;

    for (int i = 0; i < num_reads; i++) begin
      if (ar_queue.size() == 0) begin
        fail("AXI-Lite requester AR queue underflow");
        return;
      end
      item = ar_queue.pop_front();
      repeat (item.gap_cycles) @(negedge clk);
      axil_araddr  = AddrWidth'(item.addr);
      axil_arprot  = item.prot;
      axil_arvalid = 1'b1;
      wait_handshake(AxilHandshakeAr, "AR");
      if (failed) begin
        axil_arvalid = 1'b0;
        return;
      end
      @(negedge clk);
      axil_arvalid = 1'b0;
    end
  endtask

  task automatic drive_r_channel(input int num_reads);
    int stall_cycles;

    for (int i = 0; i < num_reads; i++) begin
      if (rready_stall_queue.size() == 0) begin
        fail("AXI-Lite requester R stall queue underflow");
        return;
      end
      stall_cycles = rready_stall_queue.pop_front();
      wait_response_stall(AxilHandshakeR, "R", stall_cycles);
      if (failed) begin
        return;
      end
      axil_rready = 1'b1;
      wait_handshake(AxilHandshakeR, "R");
      if (failed) begin
        axil_rready = 1'b0;
        return;
      end
      @(negedge clk);
      axil_rready = 1'b0;
    end
  endtask

  task automatic issue_write_transactions(input int num_writes);
    fork
      drive_aw_channel(num_writes);
      drive_w_channel(num_writes);
      drive_b_channel(num_writes);
    join
  endtask

  task automatic issue_read_transactions(input int num_reads);
    fork
      drive_ar_channel(num_reads);
      drive_r_channel(num_reads);
    join
  endtask

  task automatic run(input int num_writes, input int num_reads);
    fork
      issue_write_transactions(num_writes);
      issue_read_transactions(num_reads);
    join
  endtask
endmodule : br_amba_axil_requester_driver
