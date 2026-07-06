// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

import br_amba::*;
import br_amba_axi_sim_pkg::*;
import br_amba_sim_pkg::*;

// AXI timing-slice target-interface stimulus driver.
//
// This wrapper keeps the timing-slice bench naming local while reusing the
// shared configurable AXI target-side driver.
module br_amba_axi_timing_slice_driver #(
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

  logic [AxiAddrWidth-1:0] target_driver_awaddr;
  logic [AxiIdWidth-1:0] target_driver_awid;
  logic [AxiUserWidth-1:0] target_driver_awuser;
  logic [AxiDataWidth-1:0] target_driver_wdata;
  logic [AxiStrobeWidth-1:0] target_driver_wstrb;
  logic [AxiUserWidth-1:0] target_driver_wuser;
  logic [AxiAddrWidth-1:0] target_driver_araddr;
  logic [AxiIdWidth-1:0] target_driver_arid;
  logic [AxiUserWidth-1:0] target_driver_aruser;

  assign target_awaddr = AddrWidth'(target_driver_awaddr);
  assign target_awid   = IdWidth'(target_driver_awid);
  assign target_awuser = AWUserWidth'(target_driver_awuser);
  assign target_wdata  = DataWidth'(target_driver_wdata);
  assign target_wstrb  = StrobeWidth'(target_driver_wstrb);
  assign target_wuser  = WUserWidth'(target_driver_wuser);
  assign target_araddr = AddrWidth'(target_driver_araddr);
  assign target_arid   = IdWidth'(target_driver_arid);
  assign target_aruser = ARUserWidth'(target_driver_aruser);

  br_amba_axi_target_driver #(
      .TimeoutCycles(TimeoutCycles)
  ) target_driver (
      .clk,
      .rst,
      .target_awaddr(target_driver_awaddr),
      .target_awid  (target_driver_awid),
      .target_awlen,
      .target_awsize,
      .target_awburst,
      .target_awprot,
      .target_awuser(target_driver_awuser),
      .target_awvalid,
      .target_awready,
      .target_wdata (target_driver_wdata),
      .target_wstrb (target_driver_wstrb),
      .target_wuser (target_driver_wuser),
      .target_wlast,
      .target_wvalid,
      .target_wready,
      .target_bvalid,
      .target_bready,
      .target_araddr(target_driver_araddr),
      .target_arid  (target_driver_arid),
      .target_arlen,
      .target_arsize,
      .target_arburst,
      .target_arprot,
      .target_aruser(target_driver_aruser),
      .target_arvalid,
      .target_arready,
      .target_rvalid,
      .target_rready,
      .failed
  );

  task automatic init_idle();
    target_driver.init_idle();
  endtask

  task automatic run(input int num_writes, input int num_reads, input int valid_gap_cycles,
                     input int max_stall_cycles, input axi_aw_t aw_input, input axi_w_t w_input,
                     input axi_ar_t ar_input);
    target_driver.run(.num_writes(num_writes), .num_reads(num_reads),
                      .awvalid_delay(valid_gap_cycles), .wvalid_delay(valid_gap_cycles + 1),
                      .arvalid_delay(valid_gap_cycles + 2), .max_stall_cycles(max_stall_cycles),
                      .awaddr(aw_input.addr), .awid(aw_input.id), .awlen(aw_input.len),
                      .awsize(aw_input.size), .awburst(aw_input.burst), .awprot(aw_input.prot),
                      .awuser(aw_input.user), .wdata(w_input.data), .wstrb(w_input.strb),
                      .wuser(w_input.user), .wlast(w_input.last), .araddr(ar_input.addr),
                      .arid(ar_input.id), .arlen(ar_input.len), .arsize(ar_input.size),
                      .arburst(ar_input.burst), .arprot(ar_input.prot), .aruser(ar_input.user));
  endtask

endmodule : br_amba_axi_timing_slice_driver

// AXI timing-slice initiator-interface stimulus driver.
//
// This is not a generic AXI slave. It owns the timing-slice initiator-side
// B/R input valid/payload signals and AW/W/AR output ready signals.
module br_amba_axi_timing_slice_initiator_driver #(
    parameter int DataWidth = 32,
    parameter int IdWidth = 2,
    parameter int BUserWidth = 2,
    parameter int RUserWidth = 2,
    parameter int TimeoutCycles = 100
) (
    input logic clk,
    input logic rst,

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
    WaitInitAw,
    WaitInitW,
    WaitInitAr,
    WaitInitB,
    WaitInitR
  } wait_condition_e;

  typedef struct packed {
    axi_b_t payload;
    logic   valid;
  } axi_b_source_t;

  typedef struct packed {
    axi_r_t payload;
    logic   valid;
  } axi_r_source_t;

  axi_b_source_t init_b_drive;
  axi_r_source_t init_r_drive;
  logic init_awready_drive;
  logic init_wready_drive;
  logic init_arready_drive;

  assign init_awready = init_awready_drive;
  assign init_wready  = init_wready_drive;
  assign init_bid     = IdWidth'(init_b_drive.payload.id);
  assign init_buser   = BUserWidth'(init_b_drive.payload.user);
  assign init_bresp   = init_b_drive.payload.resp;
  assign init_bvalid  = init_b_drive.valid;
  assign init_arready = init_arready_drive;
  assign init_rid     = IdWidth'(init_r_drive.payload.id);
  assign init_rdata   = DataWidth'(init_r_drive.payload.data);
  assign init_ruser   = RUserWidth'(init_r_drive.payload.user);
  assign init_rresp   = init_r_drive.payload.resp;
  assign init_rlast   = init_r_drive.payload.last;
  assign init_rvalid  = init_r_drive.valid;

  task automatic init_idle();
    failed             = 1'b0;

    init_b_drive       = '0;
    init_r_drive       = '0;
    init_awready_drive = 1'b0;
    init_wready_drive  = 1'b0;
    init_arready_drive = 1'b0;
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
      WaitInitAw: is_wait_condition_met = init_awvalid && init_awready;
      WaitInitW:  is_wait_condition_met = init_wvalid && init_wready;
      WaitInitAr: is_wait_condition_met = init_arvalid && init_arready;
      WaitInitB:  is_wait_condition_met = init_bvalid && init_bready;
      WaitInitR:  is_wait_condition_met = init_rvalid && init_rready;
      default:    is_wait_condition_met = 1'b0;
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

  function automatic axi_b_t get_b_transaction(input axi_b_t base, input int index);
    get_b_transaction.id   = base.id + br_amba_axi_sim_pkg::AxiIdWidth'(IdWidth'(index));
    get_b_transaction.user = base.user + br_amba_axi_sim_pkg::AxiUserWidth'(BUserWidth'(index));
    get_b_transaction.resp = base.resp + AxiRespWidth'(index);
  endfunction

  function automatic axi_r_t get_r_transaction(input axi_r_t base, input int index);
    get_r_transaction.id   = base.id + br_amba_axi_sim_pkg::AxiIdWidth'(IdWidth'(index));
    get_r_transaction.data = base.data + br_amba_axi_sim_pkg::AxiDataWidth'(DataWidth'(index));
    get_r_transaction.resp = base.resp + AxiRespWidth'(index);
    get_r_transaction.user = base.user + br_amba_axi_sim_pkg::AxiUserWidth'(RUserWidth'(index));
    get_r_transaction.last = base.last ^ index[0];
  endfunction

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

  task automatic issue_write_transactions(input int num_transactions, input int valid_gap_cycles,
                                          input int max_stall_cycles, input axi_b_t b_input);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 3);
          drive_b(get_b_transaction(b_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_aw(get_random_stall_cycles(max_stall_cycles));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_w(get_random_stall_cycles(max_stall_cycles));
        end
      end
    join
  endtask

  task automatic issue_read_transactions(input int num_transactions, input int valid_gap_cycles,
                                         input int max_stall_cycles, input axi_r_t r_input);
    fork
      begin
        for (int i = 0; i < num_transactions; i++) begin
          wait_cycles(valid_gap_cycles + 4);
          drive_r(get_r_transaction(r_input, i));
        end
      end
      begin
        for (int i = 0; i < num_transactions; i++) begin
          accept_init_ar(get_random_stall_cycles(max_stall_cycles));
        end
      end
    join
  endtask

  task automatic run(input int num_writes, input int num_reads, input int valid_gap_cycles,
                     input int max_stall_cycles, input axi_b_t b_input, input axi_r_t r_input);
    fork
      begin
        if (num_writes > 0) begin
          issue_write_transactions(num_writes, valid_gap_cycles, max_stall_cycles, b_input);
        end
      end
      begin
        if (num_reads > 0) begin
          issue_read_transactions(num_reads, valid_gap_cycles, max_stall_cycles, r_input);
        end
      end
    join

    wait_cycles();
  endtask

endmodule : br_amba_axi_timing_slice_initiator_driver
