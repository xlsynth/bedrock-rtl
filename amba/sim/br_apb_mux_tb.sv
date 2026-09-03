// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

module br_apb_mux_tb;
  parameter int AddrWidth = 12;
  parameter int NumUpstreams = 2;
  parameter bit ExerciseProtocolViolations = 0;

  localparam int TimeoutCycles = 40;

  logic clk;
  logic rst;

  logic [NumUpstreams-1:0][AddrWidth-1:0] upstream_paddr;
  logic [NumUpstreams-1:0] upstream_psel;
  logic [NumUpstreams-1:0] upstream_penable;
  logic [NumUpstreams-1:0][br_amba::ApbProtWidth-1:0] upstream_pprot;
  logic [NumUpstreams-1:0][3:0] upstream_pstrb;
  logic [NumUpstreams-1:0] upstream_pwrite;
  logic [NumUpstreams-1:0][31:0] upstream_pwdata;
  logic [NumUpstreams-1:0][31:0] upstream_prdata;
  logic [NumUpstreams-1:0] upstream_pready;
  logic [NumUpstreams-1:0] upstream_pslverr;

  logic [AddrWidth-1:0] downstream_paddr;
  logic downstream_psel;
  logic downstream_penable;
  logic [br_amba::ApbProtWidth-1:0] downstream_pprot;
  logic [3:0] downstream_pstrb;
  logic downstream_pwrite;
  logic [31:0] downstream_pwdata;
  logic [31:0] downstream_prdata;
  logic downstream_pready;
  logic downstream_pslverr;

  br_test_driver td (
      .clk,
      .rst
  );

  br_apb_mux #(
      .AddrWidth(AddrWidth),
      .NumUpstreams(NumUpstreams)
  ) dut (
      .clk,
      .rst,
      .upstream_paddr,
      .upstream_psel,
      .upstream_penable,
      .upstream_pprot,
      .upstream_pstrb,
      .upstream_pwrite,
      .upstream_pwdata,
      .upstream_prdata,
      .upstream_pready,
      .upstream_pslverr,
      .downstream_paddr,
      .downstream_psel,
      .downstream_penable,
      .downstream_pprot,
      .downstream_pstrb,
      .downstream_pwrite,
      .downstream_pwdata,
      .downstream_prdata,
      .downstream_pready,
      .downstream_pslverr
  );

  task automatic check_downstream_request(input logic [AddrWidth-1:0] expected_addr,
                                          input logic expected_write,
                                          input logic [31:0] expected_wdata);
    td.check_integer(32'(downstream_paddr), 32'(expected_addr), "downstream PADDR mismatch");
    td.check_integer(32'(downstream_pprot), expected_write ? 3 : 5, "downstream PPROT mismatch");
    td.check_integer(32'(downstream_pstrb), expected_write ? 13 : 0, "downstream PSTRB mismatch");
    td.check(downstream_pwrite == expected_write, "downstream PWRITE mismatch");
    td.check_integer(downstream_pwdata, expected_wdata, "downstream PWDATA mismatch");
  endtask

  task automatic wait_for_downstream_select();
    bit saw_select;

    saw_select = 1'b0;
    for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
      @(posedge clk);
      if (downstream_psel) begin
        saw_select = 1'b1;
        break;
      end
    end
    td.check(saw_select, "timeout waiting for downstream PSEL");
  endtask

  task automatic drive_upstream(input int source, input logic [AddrWidth-1:0] addr,
                                input logic write, input logic [31:0] wdata,
                                input logic [31:0] expected_rdata, input logic expected_slverr);
    bit completed;

    @(negedge clk);
    upstream_paddr[source] = addr;
    upstream_psel[source] = 1'b1;
    upstream_penable[source] = 1'b0;
    upstream_pprot[source] = write ? 3'b011 : 3'b101;
    upstream_pstrb[source] = write ? 4'b1101 : 4'b0000;
    upstream_pwrite[source] = write;
    upstream_pwdata[source] = wdata;

    @(posedge clk);
    td.check(!upstream_pready[source], "upstream PREADY asserted during APB setup");

    @(negedge clk);
    upstream_penable[source] = 1'b1;
    completed = 1'b0;
    for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
      @(posedge clk);
      if (upstream_pready[source]) begin
        td.check_integer(upstream_prdata[source], expected_rdata, "upstream PRDATA mismatch");
        td.check(upstream_pslverr[source] == expected_slverr, "upstream PSLVERR mismatch");
        completed = 1'b1;
        break;
      end
    end
    td.check(completed, "timeout waiting for upstream APB completion");

    @(negedge clk);
    upstream_psel[source] = 1'b0;
    upstream_penable[source] = 1'b0;
  endtask

  task automatic expect_downstream(input int source, input logic [AddrWidth-1:0] expected_addr,
                                   input logic expected_write, input logic [31:0] expected_wdata,
                                   input int wait_cycles, input logic [31:0] rdata,
                                   input logic slverr);
    logic [NumUpstreams-1:0] expected_grant;

    expected_grant = '0;
    expected_grant[source] = 1'b1;
    wait_for_downstream_select();
    td.check(!downstream_penable, "downstream APB setup was not observed");
    td.check(upstream_pready == '0, "upstream PREADY asserted during downstream setup");
    check_downstream_request(expected_addr, expected_write, expected_wdata);

    repeat (wait_cycles) begin
      @(posedge clk);
      td.check(downstream_psel && downstream_penable, "downstream access dropped while waiting");
      td.check(upstream_pready == '0, "upstream PREADY asserted while downstream waited");
      check_downstream_request(expected_addr, expected_write, expected_wdata);
    end

    @(negedge clk);
    downstream_prdata  = rdata;
    downstream_pready  = 1'b1;
    downstream_pslverr = slverr;
    @(posedge clk);
    td.check(downstream_psel && downstream_penable, "downstream APB access was not observed");
    check_downstream_request(expected_addr, expected_write, expected_wdata);
    td.check(upstream_pready == expected_grant, "APB completion reached the wrong upstream");
    for (int i = 0; i < NumUpstreams; i++) begin
      td.check_integer(upstream_prdata[i], rdata, "upstream PRDATA was not broadcast");
    end
    td.check((upstream_pslverr & ~expected_grant) == '0,
             "APB error reached an unselected upstream");

    @(negedge clk);
    downstream_prdata  = '0;
    downstream_pready  = 1'b0;
    downstream_pslverr = 1'b0;
  endtask

  // PSEL stays asserted between transfers. A permanently ready subordinate
  // must complete each transfer in exactly two cycles, including the first.
  task automatic check_zero_wait_burst(input int source);
    logic [NumUpstreams-1:0] expected_grant;
    logic [AddrWidth-1:0] addr;
    logic write;
    logic [31:0] wdata;

    expected_grant = '0;
    expected_grant[source] = 1'b1;
    @(negedge clk);
    downstream_pready = 1'b1;
    for (int transfer = 0; transfer < 4; transfer++) begin
      addr = AddrWidth'(4 * source + transfer);
      write = 1'(transfer);
      wdata = 32'ha100_0000 | (32'(source) << 8) | 32'(transfer);
      upstream_psel[source] = 1'b1;
      upstream_penable[source] = 1'b0;
      upstream_paddr[source] = addr;
      upstream_pprot[source] = write ? 3'b011 : 3'b101;
      upstream_pstrb[source] = write ? 4'b1101 : 4'b0000;
      upstream_pwrite[source] = write;
      upstream_pwdata[source] = wdata;
      downstream_prdata = ~wdata;
      downstream_pslverr = write;

      @(posedge clk);
      td.check(downstream_psel && !downstream_penable, "extra cycle before downstream setup");
      td.check(upstream_pready == '0, "upstream completed during setup");
      check_downstream_request(addr, write, wdata);

      @(negedge clk);
      upstream_penable[source] = 1'b1;
      @(posedge clk);
      td.check(downstream_psel && downstream_penable, "extra cycle before downstream access");
      td.check(upstream_pready == expected_grant,
               "zero-wait transfer did not finish in two cycles");
      td.check_integer(upstream_prdata[source], ~wdata, "zero-wait read data mismatch");
      td.check(upstream_pslverr[source] == write, "zero-wait error response mismatch");
      check_downstream_request(addr, write, wdata);
      @(negedge clk);
    end
    upstream_psel[source] = 1'b0;
    upstream_penable[source] = 1'b0;
    downstream_pready = 1'b0;
    downstream_prdata = '0;
    downstream_pslverr = 1'b0;
  endtask

  // All masters contend at once. Waiting masters are already in upstream
  // access when selected, but must still receive a full downstream setup cycle.
  task automatic check_zero_wait_handoffs();
    logic [NumUpstreams-1:0] expected_grant;

    @(negedge clk);
    upstream_psel = '1;
    upstream_penable = '0;
    downstream_pready = 1'b1;
    downstream_prdata = 32'hcafe_1234;
    downstream_pslverr = 1'b0;
    for (int i = 0; i < NumUpstreams; i++) begin
      upstream_paddr[i]  = AddrWidth'(i);
      upstream_pprot[i]  = 3'b011;
      upstream_pstrb[i]  = 4'b1101;
      upstream_pwrite[i] = 1'b1;
      upstream_pwdata[i] = 32'habcd_0000 | 32'(i);
    end
    for (int i = 0; i < NumUpstreams; i++) begin
      expected_grant = '0;
      expected_grant[i] = 1'b1;
      @(posedge clk);
      td.check(downstream_psel && !downstream_penable, "missing setup or bubble during handoff");
      td.check(upstream_pready == '0, "waiting upstream completed during downstream setup");
      check_downstream_request(AddrWidth'(i), 1'b1, 32'habcd_0000 | 32'(i));

      @(negedge clk);
      upstream_penable = upstream_psel;
      @(posedge clk);
      td.check(downstream_psel && downstream_penable, "handoff skipped downstream access");
      td.check(upstream_pready == expected_grant, "handoff completed the wrong upstream");
      td.check_integer(upstream_prdata[i], 32'hcafe_1234, "handoff read data mismatch");
      td.check(upstream_pslverr == '0, "handoff error response mismatch");
      check_downstream_request(AddrWidth'(i), 1'b1, 32'habcd_0000 | 32'(i));

      @(negedge clk);
      upstream_psel[i] = 1'b0;
      upstream_penable[i] = 1'b0;
    end
    downstream_pready = 1'b0;
    downstream_prdata = '0;
  endtask

  task automatic check_malformed_transfer_recovers(input bit drop_select);
    @(negedge clk);
    upstream_paddr[0] = AddrWidth'(12'h620);
    upstream_psel[0] = 1'b1;
    upstream_penable[0] = 1'b0;
    upstream_pprot[0] = 3'b101;
    upstream_pstrb[0] = '0;
    upstream_pwrite[0] = 1'b0;
    upstream_pwdata[0] = 32'ha000_0620;

    @(posedge clk);
    td.check(downstream_psel && !downstream_penable,
             "malformed upstream request skipped downstream setup");
    @(negedge clk);
    upstream_penable[0] = !drop_select;
    if (drop_select) begin
      upstream_psel[0] = 1'b0;
    end

    @(posedge clk);
    td.check(downstream_psel && downstream_penable,
             "malformed upstream request prevented downstream access");

    @(negedge clk);
    upstream_penable[0] = 1'b0;

    repeat (2) begin
      @(posedge clk);
      td.check(downstream_psel && downstream_penable,
               "malformed upstream request disrupted downstream access");
      td.check(upstream_pready == '0, "malformed upstream request unexpectedly completed");
    end

    @(negedge clk);
    downstream_pready = 1'b1;
    @(posedge clk);
    td.check(downstream_psel && downstream_penable,
             "malformed upstream request prevented downstream completion");
    td.check(upstream_pready == '0, "inactive upstream unexpectedly received completion");

    @(negedge clk);
    downstream_pready = 1'b0;
    upstream_psel[0] = 1'b0;
    upstream_penable[0] = 1'b0;
    td.check(!downstream_penable,
             "arbiter did not release access after malformed upstream request");
    @(posedge clk);
    td.check(!downstream_psel, "arbiter did not become idle after all requesters withdrew");

    fork
      drive_upstream(NumUpstreams - 1, AddrWidth'(12'h740), 1'b0, 32'ha000_0740, 32'hc000_0740,
                     1'b0);
      expect_downstream(NumUpstreams - 1, AddrWidth'(12'h740), 1'b0, 32'ha000_0740, 0,
                        32'hc000_0740, 1'b0);
    join
  endtask

  initial begin
    upstream_paddr = '0;
    upstream_psel = '0;
    upstream_penable = '0;
    upstream_pprot = '0;
    upstream_pstrb = '0;
    upstream_pwrite = '0;
    upstream_pwdata = '0;
    downstream_prdata = '0;
    downstream_pready = 1'b0;
    downstream_pslverr = 1'b0;

    td.reset_dut();
    td.wait_cycles(2);
    td.check(!downstream_psel, "downstream PSEL asserted during reset/idle");
    td.check(!downstream_penable, "downstream PENABLE asserted during reset/idle");
    td.check(upstream_pready == '0, "upstream PREADY asserted during reset/idle");

    for (int i = 0; i < NumUpstreams; i++) begin
      check_zero_wait_burst(i);
    end
    check_zero_wait_handoffs();

    fork
      drive_upstream(NumUpstreams - 1, AddrWidth'(12'h120), 1'b0, 32'ha000_0120, 32'hc000_0120,
                     1'b0);
      expect_downstream(NumUpstreams - 1, AddrWidth'(12'h120), 1'b0, 32'ha000_0120, 0,
                        32'hc000_0120, 1'b0);
    join

    if (NumUpstreams > 1) begin
      fork
        drive_upstream(0, AddrWidth'(12'h240), 1'b1, 32'ha000_0240, 32'hc000_0240, 1'b0);
        drive_upstream(NumUpstreams - 1, AddrWidth'(12'h360), 1'b0, 32'ha000_0360, 32'hc000_0360,
                       1'b0);
        begin
          expect_downstream(0, AddrWidth'(12'h240), 1'b1, 32'ha000_0240, 2, 32'hc000_0240, 1'b0);
          expect_downstream(NumUpstreams - 1, AddrWidth'(12'h360), 1'b0, 32'ha000_0360, 0,
                            32'hc000_0360, 1'b0);
        end
      join

      fork
        drive_upstream(NumUpstreams - 1, AddrWidth'(12'h480), 1'b1, 32'ha000_0480, 32'hc000_0480,
                       1'b1);
        begin
          wait_for_downstream_select();
          drive_upstream(0, AddrWidth'(12'h5a0), 1'b0, 32'ha000_05a0, 32'hc000_05a0, 1'b0);
        end
        begin
          expect_downstream(NumUpstreams - 1, AddrWidth'(12'h480), 1'b1, 32'ha000_0480, 3,
                            32'hc000_0480, 1'b1);
          expect_downstream(0, AddrWidth'(12'h5a0), 1'b0, 32'ha000_05a0, 0, 32'hc000_05a0, 1'b0);
        end
      join
    end

    if (ExerciseProtocolViolations) begin
      @(negedge clk);
      upstream_penable[0] = 1'b1;
      repeat (2) begin
        @(posedge clk);
        td.check(!downstream_psel, "PENABLE without PSEL started a downstream request");
      end
      @(negedge clk);
      upstream_penable[0] = 1'b0;

      check_malformed_transfer_recovers(1'b1);
      check_malformed_transfer_recovers(1'b0);
    end

    td.finish(2);
  end
endmodule : br_apb_mux_tb
