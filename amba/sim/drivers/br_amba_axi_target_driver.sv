// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_sim_pkg::*;

// Configurable AXI target-side stimulus driver.
//
// This is not a generic AXI master. It owns AXI target-side AW/W/AR
// valid/payload signals and B/R ready signals for directed simulation benches.
module br_amba_axi_target_driver #(
    parameter int AddrWidth = 12,
    parameter int DataWidth = 32,
    parameter int IdWidth = 2,
    parameter int AWUserWidth = 2,
    parameter int WUserWidth = 2,
    parameter int ARUserWidth = 2,
    parameter int TimeoutCycles = 100,
    localparam int StrobeWidth = DataWidth / 8
) (
    input logic clk,
    input logic rst,

    output logic [AddrWidth-1:0] target_awaddr,
    output logic [IdWidth-1:0] target_awid,
    output logic [AxiBurstLenWidth-1:0] target_awlen,
    output logic [AxiBurstSizeWidth-1:0] target_awsize,
    output logic [AxiBurstTypeWidth-1:0] target_awburst,
    output logic [AxiProtWidth-1:0] target_awprot,
    output logic [AWUserWidth-1:0] target_awuser,
    output logic target_awvalid,
    input logic target_awready,
    output logic [DataWidth-1:0] target_wdata,
    output logic [StrobeWidth-1:0] target_wstrb,
    output logic [WUserWidth-1:0] target_wuser,
    output logic target_wlast,
    output logic target_wvalid,
    input logic target_wready,
    input logic target_bvalid,
    output logic target_bready,
    output logic [AddrWidth-1:0] target_araddr,
    output logic [IdWidth-1:0] target_arid,
    output logic [AxiBurstLenWidth-1:0] target_arlen,
    output logic [AxiBurstSizeWidth-1:0] target_arsize,
    output logic [AxiBurstTypeWidth-1:0] target_arburst,
    output logic [AxiProtWidth-1:0] target_arprot,
    output logic [ARUserWidth-1:0] target_aruser,
    output logic target_arvalid,
    input logic target_arready,
    input logic target_rvalid,
    output logic target_rready,

    output logic failed
);

  typedef enum int {
    WaitTargetAw,
    WaitTargetW,
    WaitTargetAr,
    WaitTargetB,
    WaitTargetR
  } wait_condition_e;

  typedef struct packed {
    axi_aw_t payload;
    logic valid;
  } axi_aw_source_t;

  typedef struct packed {
    axi_w_t payload;
    logic   valid;
  } axi_w_source_t;

  typedef struct packed {
    axi_ar_t payload;
    logic valid;
  } axi_ar_source_t;

  axi_aw_source_t target_aw_drive;
  axi_w_source_t target_w_drive;
  axi_ar_source_t target_ar_drive;
  axi_w_t queued_w_beats[$];
  logic target_bready_drive;
  logic target_rready_drive;

  clocking cb @(posedge clk);
    default input #1step;
    input target_awvalid;
    input target_awready;
    input target_wvalid;
    input target_wready;
    input target_arvalid;
    input target_arready;
    input target_bvalid;
    input target_bready;
    input target_rvalid;
    input target_rready;
  endclocking

  assign target_awaddr  = AddrWidth'(target_aw_drive.payload.addr);
  assign target_awid    = IdWidth'(target_aw_drive.payload.id);
  assign target_awlen   = target_aw_drive.payload.len;
  assign target_awsize  = target_aw_drive.payload.size;
  assign target_awburst = target_aw_drive.payload.burst;
  assign target_awprot  = target_aw_drive.payload.prot;
  assign target_awuser  = AWUserWidth'(target_aw_drive.payload.user);
  assign target_awvalid = target_aw_drive.valid;
  assign target_wdata   = DataWidth'(target_w_drive.payload.data);
  assign target_wstrb   = StrobeWidth'(target_w_drive.payload.strb);
  assign target_wuser   = WUserWidth'(target_w_drive.payload.user);
  assign target_wlast   = target_w_drive.payload.last;
  assign target_wvalid  = target_w_drive.valid;
  assign target_bready  = target_bready_drive;
  assign target_araddr  = AddrWidth'(target_ar_drive.payload.addr);
  assign target_arid    = IdWidth'(target_ar_drive.payload.id);
  assign target_arlen   = target_ar_drive.payload.len;
  assign target_arsize  = target_ar_drive.payload.size;
  assign target_arburst = target_ar_drive.payload.burst;
  assign target_arprot  = target_ar_drive.payload.prot;
  assign target_aruser  = ARUserWidth'(target_ar_drive.payload.user);
  assign target_arvalid = target_ar_drive.valid;
  assign target_rready  = target_rready_drive;

  task automatic init_idle();
    failed          = 1'b0;

    target_aw_drive = '0;
    target_w_drive  = '0;
    target_ar_drive = '0;
    queued_w_beats.delete();
    target_bready_drive = 1'b1;
    target_rready_drive = 1'b1;
  endtask

  task automatic check(input logic condition, input string message);
    if (!condition) begin
      failed = 1'b1;
      $error("%s", message);
    end
  endtask

  task automatic wait_cycles(input int cycles = 1);
    repeat (cycles) @(negedge clk);
  endtask

  function automatic logic is_wait_condition_met(input wait_condition_e condition);
    case (condition)
      WaitTargetAw: is_wait_condition_met = cb.target_awvalid && cb.target_awready;
      WaitTargetW:  is_wait_condition_met = cb.target_wvalid && cb.target_wready;
      WaitTargetAr: is_wait_condition_met = cb.target_arvalid && cb.target_arready;
      WaitTargetB:  is_wait_condition_met = cb.target_bvalid && cb.target_bready;
      WaitTargetR:  is_wait_condition_met = cb.target_rvalid && cb.target_rready;
      default:      is_wait_condition_met = 1'b0;
    endcase
  endfunction

  function automatic string wait_condition_name(input wait_condition_e condition);
    case (condition)
      WaitTargetAw: wait_condition_name = "target AW";
      WaitTargetW:  wait_condition_name = "target W";
      WaitTargetAr: wait_condition_name = "target AR";
      WaitTargetB:  wait_condition_name = "target B";
      WaitTargetR:  wait_condition_name = "target R";
      default:      wait_condition_name = "unknown AXI";
    endcase
  endfunction

  task automatic wait_for(input wait_condition_e condition);
    int timeout;

    timeout = TimeoutCycles;
    do begin
      @cb;
      timeout--;
    end while (!is_wait_condition_met(
        condition
    ) && timeout >= 0);
    check(is_wait_condition_met(condition), {
          "Timeout waiting for ", wait_condition_name(condition), " handshake"});
  endtask

  function automatic axi_aw_t get_aw_transaction(input axi_aw_t base, input int index,
                                                 input bit vary_burst_len);
    get_aw_transaction = base;
    get_aw_transaction.addr[AddrWidth-1:0] = base.addr[AddrWidth-1:0] + AddrWidth'(index);
    get_aw_transaction.id[IdWidth-1:0] = base.id[IdWidth-1:0] + IdWidth'(index);
    if (vary_burst_len) begin
      get_aw_transaction.len = base.len + AxiBurstLenWidth'(index);
    end
    get_aw_transaction.user[AWUserWidth-1:0] = base.user[AWUserWidth-1:0] + AWUserWidth'(index);
  endfunction

  function automatic axi_w_t get_w_transaction(input axi_w_t base, input int index,
                                               input bit vary_wlast);
    get_w_transaction = base;
    get_w_transaction.data[DataWidth-1:0] = base.data[DataWidth-1:0] + DataWidth'(index);
    get_w_transaction.user[WUserWidth-1:0] = base.user[WUserWidth-1:0] + WUserWidth'(index);
    if (vary_wlast) begin
      get_w_transaction.last = base.last ^ index[0];
    end
  endfunction

  function automatic axi_ar_t get_ar_transaction(input axi_ar_t base, input int index,
                                                 input bit vary_burst_len);
    get_ar_transaction = base;
    get_ar_transaction.addr[AddrWidth-1:0] = base.addr[AddrWidth-1:0] + AddrWidth'(index);
    get_ar_transaction.id[IdWidth-1:0] = base.id[IdWidth-1:0] + IdWidth'(index);
    if (vary_burst_len) begin
      get_ar_transaction.len = base.len + AxiBurstLenWidth'(index);
    end
    get_ar_transaction.user[ARUserWidth-1:0] = base.user[ARUserWidth-1:0] + ARUserWidth'(index);
  endfunction

  function automatic int get_transaction_index(input int index, input bit vary_transactions);
    if (vary_transactions) begin
      get_transaction_index = index;
    end else begin
      get_transaction_index = 0;
    end
  endfunction

  task automatic drive_aw(input axi_aw_t aw_input);
    @(negedge clk);
    target_aw_drive.payload = aw_input;
    target_aw_drive.valid   = 1'b1;
    wait_for(WaitTargetAw);
    @(negedge clk);
    target_aw_drive.valid = 1'b0;
  endtask

  task automatic drive_aw_fields(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiBurstTypeWidth-1:0] burst, input logic [AxiProtWidth-1:0] prot,
      input logic [AWUserWidth-1:0] user);
    @(negedge clk);
    target_aw_drive.payload       = '0;
    target_aw_drive.payload.addr  = addr;
    target_aw_drive.payload.id    = id;
    target_aw_drive.payload.len   = len;
    target_aw_drive.payload.size  = size;
    target_aw_drive.payload.burst = burst;
    target_aw_drive.payload.prot  = prot;
    target_aw_drive.payload.user  = user;
    target_aw_drive.valid         = 1'b1;
    wait_for(WaitTargetAw);
    @(negedge clk);
    target_aw_drive.valid = 1'b0;
  endtask

  task automatic drive_w(input axi_w_t w_input);
    @(negedge clk);
    target_w_drive.payload = w_input;
    target_w_drive.valid   = 1'b1;
    wait_for(WaitTargetW);
    @(negedge clk);
    target_w_drive.valid = 1'b0;
  endtask

  task automatic queue_w_beat(input axi_w_t w_input);
    queued_w_beats.push_back(w_input);
  endtask

  task automatic drive_queued_w(input int stall_cycles);
    axi_w_t w_input;

    wait_cycles(stall_cycles);
    check(queued_w_beats.size() > 0, "No queued AXI W beat available");
    if (queued_w_beats.size() > 0) begin
      w_input = queued_w_beats.pop_front();
      drive_w(w_input);
    end
  endtask

  task automatic drive_w_fields(input logic [DataWidth-1:0] data,
                                input logic [StrobeWidth-1:0] strb,
                                input logic [WUserWidth-1:0] user, input logic last);
    @(negedge clk);
    target_w_drive.payload      = '0;
    target_w_drive.payload.data = data;
    target_w_drive.payload.strb = strb;
    target_w_drive.payload.user = user;
    target_w_drive.payload.last = last;
    target_w_drive.valid        = 1'b1;
    wait_for(WaitTargetW);
    @(negedge clk);
    target_w_drive.valid = 1'b0;
  endtask

  task automatic drive_ar(input axi_ar_t ar_input);
    @(negedge clk);
    target_ar_drive.payload = ar_input;
    target_ar_drive.valid   = 1'b1;
    wait_for(WaitTargetAr);
    @(negedge clk);
    target_ar_drive.valid = 1'b0;
  endtask

  task automatic drive_ar_fields(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiBurstTypeWidth-1:0] burst, input logic [AxiProtWidth-1:0] prot,
      input logic [ARUserWidth-1:0] user);
    @(negedge clk);
    target_ar_drive.payload       = '0;
    target_ar_drive.payload.addr  = addr;
    target_ar_drive.payload.id    = id;
    target_ar_drive.payload.len   = len;
    target_ar_drive.payload.size  = size;
    target_ar_drive.payload.burst = burst;
    target_ar_drive.payload.prot  = prot;
    target_ar_drive.payload.user  = user;
    target_ar_drive.valid         = 1'b1;
    wait_for(WaitTargetAr);
    @(negedge clk);
    target_ar_drive.valid = 1'b0;
  endtask

  task automatic accept_target_b(input int stall_cycles);
    if (stall_cycles > 0) begin
      target_bready_drive = 1'b0;
      wait_cycles(stall_cycles);
    end
    target_bready_drive = 1'b1;
    wait_for(WaitTargetB);
  endtask

  task automatic accept_target_r(input int stall_cycles);
    if (stall_cycles > 0) begin
      target_rready_drive = 1'b0;
      wait_cycles(stall_cycles);
    end
    target_rready_drive = 1'b1;
    wait_for(WaitTargetR);
  endtask

  task automatic run_write_burst(input axi_aw_t aw_input, input int max_stall_cycles,
                                 input int response_stall_cycles);
    int unsigned beats;

    beats = int'(aw_input.len) + 1;
    check(queued_w_beats.size() >= beats, "Too few queued AXI W beats for write burst");
    fork
      drive_aw(aw_input);
      begin
        for (int unsigned beat = 0; beat < beats; beat++) begin
          drive_queued_w(get_random_stall_cycles(max_stall_cycles));
        end
      end
      accept_target_b(response_stall_cycles);
    join
  endtask

  task automatic run_read_burst_fields(
      input logic [AddrWidth-1:0] addr, input logic [IdWidth-1:0] id,
      input logic [AxiBurstLenWidth-1:0] len, input logic [AxiBurstSizeWidth-1:0] size,
      input logic [AxiBurstTypeWidth-1:0] burst, input logic [AxiProtWidth-1:0] prot,
      input logic [ARUserWidth-1:0] aruser, input int max_stall_cycles);
    int unsigned beats;

    beats = int'(len) + 1;
    fork
      drive_ar_fields(addr, id, len, size, burst, prot, aruser);
      begin
        for (int unsigned beat = 0; beat < beats; beat++) begin
          accept_target_r(get_random_stall_cycles(max_stall_cycles));
        end
      end
    join
  endtask

  task automatic issue_write_transactions(
      input int num_transactions, input int awvalid_delay, input int wvalid_delay,
      input int max_stall_cycles, input axi_aw_t aw_input, input axi_w_t w_input,
      input bit vary_transactions, input bit vary_burst_len, input bit vary_wlast);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(awvalid_delay);
          drive_aw(get_aw_transaction(
                   aw_input, get_transaction_index(i, vary_transactions), vary_burst_len));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(wvalid_delay);
          drive_w(get_w_transaction(w_input, get_transaction_index(i, vary_transactions), vary_wlast
                  ));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_target_b(get_random_stall_cycles(max_stall_cycles));
        end
      end
    join
  endtask

  function automatic int get_num_r_beats(input axi_ar_t ar_input, input int index,
                                         input bit accept_r_burst_len, input bit vary_transactions,
                                         input bit vary_burst_len);
    if (accept_r_burst_len) begin
      get_num_r_beats = int'(get_ar_transaction(ar_input, get_transaction_index(
                                                index, vary_transactions), vary_burst_len).len) + 1;
    end else begin
      get_num_r_beats = 1;
    end
  endfunction

  task automatic issue_read_transactions(input int num_transactions, input int arvalid_delay,
                                         input int max_stall_cycles, input axi_ar_t ar_input,
                                         input bit accept_r_burst_len, input bit vary_transactions,
                                         input bit vary_burst_len);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(arvalid_delay);
          drive_ar(get_ar_transaction(
                   ar_input, get_transaction_index(i, vary_transactions), vary_burst_len));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          for (
              int beat = 0;
              beat < get_num_r_beats(
                  ar_input, i, accept_r_burst_len, vary_transactions, vary_burst_len
              );
              beat++
          ) begin
            accept_target_r(get_random_stall_cycles(max_stall_cycles));
          end
        end
      end
    join
  endtask

  task automatic run(input int num_writes = 0, input int num_reads = 0, input int awvalid_delay = 0,
                     input int wvalid_delay = 0, input int arvalid_delay = 0,
                     input int max_stall_cycles = 0, input axi_aw_t aw_input = '0,
                     input axi_w_t w_input = '0, input axi_ar_t ar_input = '0,
                     input bit accept_r_burst_len = 0, input bit vary_transactions = 1,
                     input bit vary_burst_len = 1, input bit vary_wlast = 1);
    fork
      begin
        if (num_writes > 0) begin
          issue_write_transactions(num_writes, awvalid_delay, wvalid_delay, max_stall_cycles,
                                   aw_input, w_input, vary_transactions, vary_burst_len,
                                   vary_wlast);
        end
      end
      begin
        if (num_reads > 0) begin
          issue_read_transactions(num_reads, arvalid_delay, max_stall_cycles, ar_input,
                                  accept_r_burst_len, vary_transactions, vary_burst_len);
        end
      end
    join

    wait_cycles();
  endtask

endmodule : br_amba_axi_target_driver
