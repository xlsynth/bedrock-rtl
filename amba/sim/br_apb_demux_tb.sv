// SPDX-License-Identifier: Apache-2.0

`timescale 1ns / 1ps

module br_apb_demux_tb;
  parameter int AddrWidth = 12;
  parameter int NumDownstreams = 2;
  parameter int NumRetimeStagesPerDownstream = 0;
  parameter bit HasDefaultDownstream = 0;

  localparam int NumAddressRanges = HasDefaultDownstream ? NumDownstreams - 1 : NumDownstreams;
  localparam int NumRetimeStages[NumDownstreams] = '{0: 0, default: NumRetimeStagesPerDownstream};
  localparam bit NormalizeDownstreamAddress[NumAddressRanges] = '{default: 1};
  localparam logic [AddrWidth-1:0] AddrMask = {1'b0, {(AddrWidth - 1) {1'b1}}};
  localparam logic [NumDownstreams-1:0][AddrWidth-1:0] DownstreamAddrMask =
      {NumDownstreams{AddrMask}};
  localparam int RangeSize = 256;
  localparam int TimeoutCycles = 40;
  localparam logic [31:0] NoiseRdata = 32'hbad0_bad0;

  logic clk;
  logic rst;

  logic [AddrWidth-1:0] upstream_paddr;
  logic upstream_psel;
  logic upstream_penable;
  logic [br_amba::ApbProtWidth-1:0] upstream_pprot;
  logic [3:0] upstream_pstrb;
  logic upstream_pwrite;
  logic [31:0] upstream_pwdata;
  logic [31:0] upstream_prdata;
  logic upstream_pready;
  logic upstream_pslverr;

  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_base;
  logic [NumAddressRanges-1:0][AddrWidth-1:0] downstream_addr_size;

  logic [NumDownstreams-1:0][AddrWidth-1:0] downstream_paddr;
  logic [NumDownstreams-1:0] downstream_psel;
  logic [NumDownstreams-1:0] downstream_penable;
  logic [NumDownstreams-1:0][br_amba::ApbProtWidth-1:0] downstream_pprot;
  logic [NumDownstreams-1:0][3:0] downstream_pstrb;
  logic [NumDownstreams-1:0] downstream_pwrite;
  logic [NumDownstreams-1:0][31:0] downstream_pwdata;
  logic [NumDownstreams-1:0][31:0] downstream_prdata;
  logic [NumDownstreams-1:0] downstream_pready;
  logic [NumDownstreams-1:0] downstream_pslverr;

  br_test_driver td (
      .clk,
      .rst
  );

  br_apb_demux #(
      .AddrWidth(AddrWidth),
      .NumDownstreams(NumDownstreams),
      .NumRetimeStages(NumRetimeStages),
      .HasDefaultDownstream(HasDefaultDownstream),
      .NormalizeDownstreamAddress(NormalizeDownstreamAddress),
      .UpstreamAddrMask(AddrMask),
      .DownstreamAddrMask(DownstreamAddrMask)
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
      .downstream_addr_base,
      .downstream_addr_size,
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

  task automatic check_downstream_request(
      input int expected_dest, input logic [AddrWidth-1:0] expected_addr,
      input logic [br_amba::ApbProtWidth-1:0] expected_prot, input logic [3:0] expected_strb,
      input logic expected_write, input logic [31:0] expected_wdata);
    td.check_integer(32'(downstream_psel), 1 << expected_dest, "downstream PSEL mismatch");
    td.check_integer(32'(downstream_paddr[expected_dest]), 32'(expected_addr),
                     "downstream PADDR mismatch");
    td.check_integer(32'(downstream_pprot[expected_dest]), 32'(expected_prot),
                     "downstream PPROT mismatch");
    td.check_integer(32'(downstream_pstrb[expected_dest]), 32'(expected_strb),
                     "downstream PSTRB mismatch");
    td.check_integer(32'(downstream_pwrite[expected_dest]), 32'(expected_write),
                     "downstream PWRITE mismatch");
    td.check_integer(downstream_pwdata[expected_dest], expected_wdata,
                     "downstream PWDATA mismatch");
  endtask

  task automatic drive_upstream(input logic [AddrWidth-1:0] addr,
                                input logic [br_amba::ApbProtWidth-1:0] prot,
                                input logic [3:0] strb, input logic write, input logic [31:0] wdata,
                                input logic [31:0] expected_rdata, input logic expected_slverr);
    bit completed;

    @(negedge clk);
    upstream_paddr = addr;
    upstream_psel = 1'b1;
    upstream_penable = 1'b0;
    upstream_pprot = prot;
    upstream_pstrb = strb;
    upstream_pwrite = write;
    upstream_pwdata = wdata;

    @(posedge clk);
    td.check(!upstream_pready, "PREADY asserted during APB setup");
    td.check(!upstream_pslverr, "PSLVERR asserted during APB setup");

    @(negedge clk);
    upstream_penable = 1'b1;
    completed = 1'b0;
    for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
      @(posedge clk);
      if (upstream_pready) begin
        td.check_integer(upstream_prdata, expected_rdata, "upstream PRDATA mismatch");
        td.check(upstream_pslverr == expected_slverr, "upstream PSLVERR mismatch");
        completed = 1'b1;
        break;
      end
    end
    td.check(completed, "timeout waiting for upstream APB completion");

    @(negedge clk);
    upstream_psel = 1'b0;
    upstream_penable = 1'b0;
  endtask

  task automatic drive_downstream(
      input int expected_dest, input logic [AddrWidth-1:0] expected_addr,
      input logic [br_amba::ApbProtWidth-1:0] expected_prot, input logic [3:0] expected_strb,
      input logic expected_write, input logic [31:0] expected_wdata, input int wait_cycles,
      input logic [31:0] rdata, input logic slverr);
    bit saw_setup;
    bit saw_access;

    downstream_prdata  = {NumDownstreams{NoiseRdata}};
    downstream_pready  = '1;
    downstream_pslverr = '1;
    if (expected_dest < 0) begin
      for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
        @(posedge clk);
        if (upstream_psel) begin
          td.check(downstream_psel == '0, "decode miss asserted downstream PSEL");
          td.check(downstream_penable == '0, "decode miss asserted downstream PENABLE");
        end
        if (upstream_pready) begin
          break;
        end
      end
      return;
    end

    downstream_prdata[expected_dest] = '0;
    downstream_pready[expected_dest] = 1'b0;
    downstream_pslverr[expected_dest] = 1'b0;

    saw_setup = 1'b0;
    for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
      @(posedge clk);
      if (downstream_psel[expected_dest]) begin
        td.check(!downstream_penable[expected_dest], "downstream APB setup was not observed");
        check_downstream_request(expected_dest, expected_addr, expected_prot, expected_strb,
                                 expected_write, expected_wdata);
        saw_setup = 1'b1;
        break;
      end
    end
    td.check(saw_setup, "timeout waiting for downstream APB setup");

    saw_access = 1'b0;
    for (int cycle = 0; cycle < TimeoutCycles; cycle++) begin
      @(posedge clk);
      if (downstream_penable[expected_dest]) begin
        check_downstream_request(expected_dest, expected_addr, expected_prot, expected_strb,
                                 expected_write, expected_wdata);
        saw_access = 1'b1;
        break;
      end
    end
    td.check(saw_access, "timeout waiting for downstream APB access");

    repeat (wait_cycles) begin
      @(posedge clk);
      td.check(downstream_psel[expected_dest] && downstream_penable[expected_dest],
               "downstream APB access dropped while waiting");
      check_downstream_request(expected_dest, expected_addr, expected_prot, expected_strb,
                               expected_write, expected_wdata);
    end

    @(negedge clk);
    downstream_prdata[expected_dest]  = rdata;
    downstream_pready[expected_dest]  = 1'b1;
    downstream_pslverr[expected_dest] = slverr;
    @(posedge clk);
    td.check(downstream_psel[expected_dest] && downstream_penable[expected_dest],
             "downstream APB access dropped before completion");
  endtask

  task automatic send_and_check(input logic [AddrWidth-1:0] addr, input int expected_dest,
                                input logic write, input int wait_cycles,
                                input logic expected_slverr);
    logic [AddrWidth-1:0] expected_addr;
    logic [br_amba::ApbProtWidth-1:0] prot;
    logic [3:0] strb;
    logic [31:0] wdata;
    logic [31:0] rdata;

    prot = write ? 3'b011 : 3'b101;
    strb = write ? 4'b1011 : 4'b0000;
    wdata = 32'hd000_0000 | 32'(addr);
    rdata = 32'hc000_0000 | 32'(addr);
    expected_addr = addr & AddrMask;
    if (expected_dest >= 0 && expected_dest < NumAddressRanges) begin
      expected_addr = (addr - downstream_addr_base[expected_dest]) & AddrMask;
    end
    if (expected_dest < 0) begin
      rdata = '0;
    end

    fork
      drive_upstream(addr, prot, strb, write, wdata, rdata, expected_slverr);
      drive_downstream(expected_dest, expected_addr, prot, strb, write, wdata, wait_cycles, rdata,
                       expected_slverr);
    join
    @(negedge clk);
    downstream_prdata  = '0;
    downstream_pready  = '0;
    downstream_pslverr = '0;
  endtask

  initial begin
    logic [AddrWidth-1:0] addr;
    int miss_dest;

    upstream_paddr = '0;
    upstream_psel = 1'b0;
    upstream_penable = 1'b0;
    upstream_pprot = '0;
    upstream_pstrb = '0;
    upstream_pwrite = 1'b0;
    upstream_pwdata = '0;
    downstream_prdata = '0;
    downstream_pready = '0;
    downstream_pslverr = '0;

    for (int i = 0; i < NumAddressRanges; i++) begin
      downstream_addr_base[i] = AddrWidth'((i + 1) * RangeSize);
      downstream_addr_size[i] = AddrWidth'(RangeSize);
    end

    td.reset_dut();
    td.wait_cycles(2);
    td.check(downstream_psel == '0, "downstream PSEL asserted during reset/idle");
    td.check(downstream_penable == '0, "downstream PENABLE asserted during reset/idle");
    td.check(!upstream_pready, "upstream PREADY asserted during reset/idle");
    td.check(!upstream_pslverr, "upstream PSLVERR asserted during reset/idle");

    for (int i = 0; i < NumAddressRanges; i++) begin
      send_and_check(downstream_addr_base[i], i, 1'b1, 0, 1'b0);
      send_and_check(downstream_addr_base[i] + AddrWidth'(RangeSize - 1), i, 1'b0, 2, 1'b1);
    end

    addr = downstream_addr_base[0] + AddrWidth'(32);
    addr[AddrWidth-1] = 1'b1;
    send_and_check(addr, 0, 1'b0, 1, 1'b0);

    miss_dest = HasDefaultDownstream ? NumDownstreams - 1 : -1;
    addr = AddrWidth'((NumAddressRanges + 2) * RangeSize);
    send_and_check(addr, miss_dest, 1'b1, 0, !HasDefaultDownstream);

    downstream_addr_size[0] = '0;
    send_and_check(downstream_addr_base[0], miss_dest, 1'b0, 1, !HasDefaultDownstream);

    td.finish();
  end
endmodule : br_apb_demux_tb
