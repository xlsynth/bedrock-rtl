// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;

// AXI timing-slice stimulus driver.
//
// This is not a generic AXI master or slave driver. It owns only the timing-slice
// input valid/payload signals and output ready signals, and drives deterministic
// per-channel ready/valid traffic with configurable gaps and stalls.
module br_amba_axi_timing_slice_driver #(
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

    input logic init_awvalid,
    output logic init_awready,
    input logic init_wvalid,
    output logic init_wready,
    output logic [IdWidth-1:0] init_bid,
    output logic [BUserWidth-1:0] init_buser,
    output logic [AxiRespWidth-1:0] init_bresp,
    output logic init_bvalid,
    input logic init_bready,
    input logic init_arvalid,
    output logic init_arready,
    output logic [IdWidth-1:0] init_rid,
    output logic [DataWidth-1:0] init_rdata,
    output logic [RUserWidth-1:0] init_ruser,
    output logic [AxiRespWidth-1:0] init_rresp,
    output logic init_rlast,
    output logic init_rvalid,
    input logic init_rready,

    output logic failed
);

  typedef enum int {
    WaitTargetAw,
    WaitTargetW,
    WaitTargetAr,
    WaitInitB,
    WaitInitR,
    WaitInitAw,
    WaitInitW,
    WaitInitAr,
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

  typedef struct packed {
    axi_b_t payload;
    logic   valid;
  } axi_b_source_t;

  typedef struct packed {
    axi_r_t payload;
    logic   valid;
  } axi_r_source_t;

  axi_aw_source_t target_aw_drive;
  axi_w_source_t target_w_drive;
  axi_ar_source_t target_ar_drive;
  axi_b_source_t init_b_drive;
  axi_r_source_t init_r_drive;
  logic init_awready_drive;
  logic init_wready_drive;
  logic init_arready_drive;
  logic target_bready_drive;
  logic target_rready_drive;

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

  assign init_awready   = init_awready_drive;
  assign init_wready    = init_wready_drive;
  assign init_bid       = IdWidth'(init_b_drive.payload.id);
  assign init_buser     = BUserWidth'(init_b_drive.payload.user);
  assign init_bresp     = init_b_drive.payload.resp;
  assign init_bvalid    = init_b_drive.valid;
  assign init_arready   = init_arready_drive;
  assign init_rid       = IdWidth'(init_r_drive.payload.id);
  assign init_rdata     = DataWidth'(init_r_drive.payload.data);
  assign init_ruser     = RUserWidth'(init_r_drive.payload.user);
  assign init_rresp     = init_r_drive.payload.resp;
  assign init_rlast     = init_r_drive.payload.last;
  assign init_rvalid    = init_r_drive.valid;

  task automatic init_idle();
    failed              = 1'b0;

    target_aw_drive     = '0;
    target_w_drive      = '0;
    target_ar_drive     = '0;
    init_b_drive        = '0;
    init_r_drive        = '0;
    init_awready_drive  = 1'b0;
    init_wready_drive   = 1'b0;
    init_arready_drive  = 1'b0;
    target_bready_drive = 1'b0;
    target_rready_drive = 1'b0;
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

  function automatic int get_stall_cycles(input int index, input int max_stall_cycles,
                                          input int salt);
    if (max_stall_cycles == 0) begin
      return 0;
    end
    return (((index + 1) * salt) ^ (salt >> 1)) % (max_stall_cycles + 1);
  endfunction

  function automatic logic is_wait_condition_met(input wait_condition_e condition);
    case (condition)
      WaitTargetAw: is_wait_condition_met = target_awvalid && target_awready;
      WaitTargetW:  is_wait_condition_met = target_wvalid && target_wready;
      WaitTargetAr: is_wait_condition_met = target_arvalid && target_arready;
      WaitInitB:    is_wait_condition_met = init_bvalid && init_bready;
      WaitInitR:    is_wait_condition_met = init_rvalid && init_rready;
      WaitInitAw:   is_wait_condition_met = init_awvalid && init_awready;
      WaitInitW:    is_wait_condition_met = init_wvalid && init_wready;
      WaitInitAr:   is_wait_condition_met = init_arvalid && init_arready;
      WaitTargetB:  is_wait_condition_met = target_bvalid && target_bready;
      WaitTargetR:  is_wait_condition_met = target_rvalid && target_rready;
      default:      is_wait_condition_met = 1'b0;
    endcase
  endfunction

  task automatic wait_for(input wait_condition_e condition, input string timeout_message);
    int timeout;

    timeout = TimeoutCycles;
    while (!is_wait_condition_met(
        condition
    ) && timeout > 0) begin
      @(posedge clk);
      timeout--;
    end
    check(is_wait_condition_met(condition), timeout_message);
  endtask

  function automatic axi_aw_t get_aw_transaction(input axi_aw_t base, input int index);
    get_aw_transaction.addr  = base.addr + AddrWidth'(index);
    get_aw_transaction.id    = base.id + IdWidth'(index);
    get_aw_transaction.len   = base.len + AxiBurstLenWidth'(index);
    get_aw_transaction.size  = base.size;
    get_aw_transaction.burst = base.burst;
    get_aw_transaction.prot  = base.prot;
    get_aw_transaction.user  = base.user + AWUserWidth'(index);
  endfunction

  function automatic axi_w_t get_w_transaction(input axi_w_t base, input int index);
    get_w_transaction.data = base.data + DataWidth'(index);
    get_w_transaction.strb = base.strb;
    get_w_transaction.user = base.user + WUserWidth'(index);
    get_w_transaction.last = base.last ^ index[0];
  endfunction

  function automatic axi_ar_t get_ar_transaction(input axi_ar_t base, input int index);
    get_ar_transaction.addr  = base.addr + AddrWidth'(index);
    get_ar_transaction.id    = base.id + IdWidth'(index);
    get_ar_transaction.len   = base.len + AxiBurstLenWidth'(index);
    get_ar_transaction.size  = base.size;
    get_ar_transaction.burst = base.burst;
    get_ar_transaction.prot  = base.prot;
    get_ar_transaction.user  = base.user + ARUserWidth'(index);
  endfunction

  function automatic axi_b_t get_b_transaction(input axi_b_t base, input int index);
    get_b_transaction.id   = base.id + IdWidth'(index);
    get_b_transaction.user = base.user + BUserWidth'(index);
    get_b_transaction.resp = base.resp + AxiRespWidth'(index);
  endfunction

  function automatic axi_r_t get_r_transaction(input axi_r_t base, input int index);
    get_r_transaction.id   = base.id + IdWidth'(index);
    get_r_transaction.data = base.data + DataWidth'(index);
    get_r_transaction.resp = base.resp + AxiRespWidth'(index);
    get_r_transaction.user = base.user + RUserWidth'(index);
    get_r_transaction.last = base.last ^ index[0];
  endfunction

  task automatic drive_aw(input axi_aw_t aw_input);
    @(negedge clk);
    target_aw_drive.payload = aw_input;
    target_aw_drive.valid   = 1'b1;
    wait_for(WaitTargetAw, "Timeout waiting for target AW handshake");
    @(negedge clk);
    target_aw_drive.valid = 1'b0;
  endtask

  task automatic drive_w(input axi_w_t w_input);
    @(negedge clk);
    target_w_drive.payload = w_input;
    target_w_drive.valid   = 1'b1;
    wait_for(WaitTargetW, "Timeout waiting for target W handshake");
    @(negedge clk);
    target_w_drive.valid = 1'b0;
  endtask

  task automatic drive_ar(input axi_ar_t ar_input);
    @(negedge clk);
    target_ar_drive.payload = ar_input;
    target_ar_drive.valid   = 1'b1;
    wait_for(WaitTargetAr, "Timeout waiting for target AR handshake");
    @(negedge clk);
    target_ar_drive.valid = 1'b0;
  endtask

  task automatic drive_b(input axi_b_t b_input);
    @(negedge clk);
    init_b_drive.payload = b_input;
    init_b_drive.valid   = 1'b1;
    wait_for(WaitInitB, "Timeout waiting for init B handshake");
    @(negedge clk);
    init_b_drive.valid = 1'b0;
  endtask

  task automatic drive_r(input axi_r_t r_input);
    @(negedge clk);
    init_r_drive.payload = r_input;
    init_r_drive.valid   = 1'b1;
    wait_for(WaitInitR, "Timeout waiting for init R handshake");
    @(negedge clk);
    init_r_drive.valid = 1'b0;
  endtask

  task automatic accept_init_aw(input int stall_cycles);
    init_awready_drive = 1'b0;
    wait_cycles(stall_cycles);
    init_awready_drive = 1'b1;
    wait_for(WaitInitAw, "Timeout waiting for init AW handshake");
    @(negedge clk);
    init_awready_drive = 1'b0;
  endtask

  task automatic accept_init_w(input int stall_cycles);
    init_wready_drive = 1'b0;
    wait_cycles(stall_cycles);
    init_wready_drive = 1'b1;
    wait_for(WaitInitW, "Timeout waiting for init W handshake");
    @(negedge clk);
    init_wready_drive = 1'b0;
  endtask

  task automatic accept_init_ar(input int stall_cycles);
    init_arready_drive = 1'b0;
    wait_cycles(stall_cycles);
    init_arready_drive = 1'b1;
    wait_for(WaitInitAr, "Timeout waiting for init AR handshake");
    @(negedge clk);
    init_arready_drive = 1'b0;
  endtask

  task automatic accept_target_b(input int stall_cycles);
    target_bready_drive = 1'b0;
    wait_cycles(stall_cycles);
    target_bready_drive = 1'b1;
    wait_for(WaitTargetB, "Timeout waiting for target B handshake");
    @(negedge clk);
    target_bready_drive = 1'b0;
  endtask

  task automatic accept_target_r(input int stall_cycles);
    target_rready_drive = 1'b0;
    wait_cycles(stall_cycles);
    target_rready_drive = 1'b1;
    wait_for(WaitTargetR, "Timeout waiting for target R handshake");
    @(negedge clk);
    target_rready_drive = 1'b0;
  endtask

  task automatic issue_write_transactions(input int num_transactions, input int valid_gap_cycles,
                                          input int max_stall_cycles, input axi_aw_t aw_input,
                                          input axi_w_t w_input, input axi_b_t b_input);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles);
          drive_aw(get_aw_transaction(aw_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 1);
          drive_w(get_w_transaction(w_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 3);
          drive_b(get_b_transaction(b_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_aw(get_stall_cycles(i, max_stall_cycles, 101));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_w(get_stall_cycles(i, max_stall_cycles, 103));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_target_b(get_stall_cycles(i, max_stall_cycles, 109));
        end
      end
    join
  endtask

  task automatic issue_read_transactions(input int num_transactions, input int valid_gap_cycles,
                                         input int max_stall_cycles, input axi_ar_t ar_input,
                                         input axi_r_t r_input);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 2);
          drive_ar(get_ar_transaction(ar_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 4);
          drive_r(get_r_transaction(r_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_ar(get_stall_cycles(i, max_stall_cycles, 107));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_target_r(get_stall_cycles(i, max_stall_cycles, 113));
        end
      end
    join
  endtask

  task automatic run(input int num_writes, input int num_reads, input int valid_gap_cycles,
                     input int max_stall_cycles, input axi_aw_t aw_input, input axi_w_t w_input,
                     input axi_ar_t ar_input, input axi_b_t b_input, input axi_r_t r_input);
    fork
      begin
        if (num_writes > 0) begin
          issue_write_transactions(num_writes, valid_gap_cycles, max_stall_cycles, aw_input,
                                   w_input, b_input);
        end
      end
      begin
        if (num_reads > 0) begin
          issue_read_transactions(num_reads, valid_gap_cycles, max_stall_cycles, ar_input, r_input);
        end
      end
    join

    wait_cycles();
  endtask

endmodule : br_amba_axi_timing_slice_driver
