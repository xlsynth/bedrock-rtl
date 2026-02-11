// SPDX-License-Identifier: Apache-2.0
//
// Basic unit test for br_csr_mem_interface.

module br_csr_mem_interface_tb;
  parameter int TimeoutCycles = 100;
  parameter int CsrAddrWidth = 16;
  parameter int CsrDataWidth = 32;
  parameter bit RegisterMemOutputs = 0;
  parameter bit RegisterResponseOutputs = 0;
  parameter int MemWidth = CsrDataWidth;
  localparam int MemDepth = (2 ** CsrAddrWidth) / (MemWidth / 8);
  localparam int MemAddrWidth = br_math::clamped_clog2(MemDepth);
  localparam int CsrStrobeWidth = CsrDataWidth / 8;
  localparam int MemStrobeWidth = MemWidth / 8;

  logic clk;
  logic rst;

  logic req_valid;
  logic req_write;
  logic [CsrAddrWidth-1:0] req_addr;
  logic [CsrDataWidth-1:0] req_wdata;
  logic [CsrStrobeWidth-1:0] req_wstrb;
  logic req_privileged;
  logic req_secure;
  logic req_abort;

  logic resp_valid;
  logic [CsrDataWidth-1:0] resp_rdata;
  logic resp_slverr;
  logic resp_decerr;

  logic mem_access_valid;
  logic [MemAddrWidth-1:0] mem_access_addr;
  logic mem_access_wr_en;
  logic [MemWidth-1:0] mem_access_wr_data;
  logic [MemStrobeWidth-1:0] mem_access_wr_strb;
  logic mem_access_ready;

  logic mem_read_data_valid;
  logic [MemWidth-1:0] mem_read_data;
  logic mem_read_data_err;

  br_csr_mem_interface #(
      .CsrAddrWidth(CsrAddrWidth),
      .CsrDataWidth(CsrDataWidth),
      .MemDepth(MemDepth),
      .MemWidth(MemWidth),
      .RegisterMemOutputs(RegisterMemOutputs),
      .RegisterResponseOutputs(RegisterResponseOutputs),
      // TODO(zhemao): Check that partial writes work correctly.
      .EnablePartialWrites(0)
  ) dut (
      .clk,
      .rst,
      .req_valid,
      .req_write,
      .req_addr,
      .req_wdata,
      .req_wstrb,
      .req_privileged,
      .req_secure,
      .req_abort,
      .resp_valid,
      .resp_rdata,
      .resp_slverr,
      .resp_decerr,
      .mem_access_valid,
      .mem_access_addr,
      .mem_access_wr_en,
      .mem_access_wr_data,
      .mem_access_wr_strb,
      .mem_access_ready,
      .mem_read_data_valid,
      .mem_read_data,
      .mem_read_data_err
  );

  br_test_driver #(
      .ResetCycles(5)
  ) td (
      .clk,
      .rst
  );

  task automatic send_write_req(input logic [CsrAddrWidth-1:0] addr,
                                input logic [CsrDataWidth-1:0] wdata,
                                input logic [CsrStrobeWidth-1:0] wstrb);
    @(negedge clk);
    req_valid = 1'b1;
    req_write = 1'b1;
    req_addr  = addr;
    req_wdata = wdata;
    req_wstrb = wstrb;

    @(negedge clk);
    req_valid = 1'b0;
    req_write = 1'b0;
  endtask

  task automatic send_read_req(input logic [CsrAddrWidth-1:0] addr);
    @(negedge clk);
    req_valid = 1'b1;
    req_write = 1'b0;
    req_addr  = addr;
    req_wdata = '0;
    req_wstrb = '0;

    @(negedge clk);
    req_valid = 1'b0;
  endtask

  task automatic pulse_abort();
    @(negedge clk);
    req_abort = 1'b1;
    @(negedge clk);
    req_abort = 1'b0;
  endtask

  task automatic pulse_read_data(input logic [MemWidth-1:0] data, input logic err);
    @(negedge clk);
    mem_read_data_valid = 1'b1;
    mem_read_data = data;
    mem_read_data_err = err;

    @(negedge clk);
    mem_read_data_valid = 1'b0;
    mem_read_data = '0;
    mem_read_data_err = 1'b0;
  endtask

  task automatic wait_for_write_req(input logic [MemAddrWidth-1:0] expected_addr,
                                    input logic [MemWidth-1:0] expected_wdata,
                                    input logic [MemStrobeWidth-1:0] expected_wstrb);
    int timeout;
    timeout = 0;

    @(posedge clk);
    while (!mem_access_valid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for memory write request");
    td.check(mem_access_wr_en, "Memory write enable should be 1");
    td.check_integer(mem_access_addr, expected_addr, "Memory write address mismatch");
    td.check_integer(mem_access_wr_data, expected_wdata, "Memory write data mismatch");
    td.check_integer(mem_access_wr_strb, expected_wstrb, "Memory write strobe mismatch");
  endtask

  task automatic wait_for_read_req(input logic [MemAddrWidth-1:0] expected_addr);
    int timeout;
    timeout = 0;

    @(posedge clk);
    while (!mem_access_valid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for memory read request");
    td.check(!mem_access_wr_en, "Memory write enable should be 0");
    td.check_integer(mem_access_addr, expected_addr, "Memory read address mismatch");
  endtask

  task automatic wait_for_resp(input logic [CsrDataWidth-1:0] expected_rdata,
                               input logic expected_slverr);
    int timeout;
    timeout = 0;

    @(posedge clk);
    while (!resp_valid && timeout < TimeoutCycles) begin
      @(posedge clk);
      timeout++;
    end

    td.check(timeout < TimeoutCycles, "Timeout waiting for CSR response");
    td.check_integer(resp_rdata, expected_rdata, "Response rdata mismatch");
    td.check_integer(resp_slverr, expected_slverr, "Response slverr mismatch");
    td.check_integer(resp_decerr, 1'b0, "Response decerr should always be 0");
  endtask

  initial begin
    req_valid = 1'b0;
    req_write = 1'b0;
    req_addr = '0;
    req_wdata = '0;
    req_wstrb = '0;
    req_privileged = 1'b0;
    req_secure = 1'b0;
    req_abort = 1'b0;

    mem_access_ready = 1'b0;
    mem_read_data_valid = 1'b0;
    mem_read_data = '0;
    mem_read_data_err = 1'b0;

    td.reset_dut();
    td.wait_cycles(2);

    $display("Checking immediate write request and response");
    mem_access_ready = 1'b1;
    fork
      send_write_req(16'h0010, 32'h12345678, 4'b1100);
      wait_for_write_req(15'h0008, 16'h1234, 2'b11);
      wait_for_resp('0, 1'b0);
    join

    $display("Checking buffered write request, then release");
    mem_access_ready = 1'b0;
    fork
      send_write_req(16'h0020, 32'h89ABCDEF, 4'b0011);
      wait_for_write_req(15'h0010, 16'hCDEF, 2'b11);
    join
    td.wait_cycles(2);
    td.check(mem_access_valid, "Buffered write request should remain valid while backpressured");
    td.check(mem_access_wr_en, "Memory write enable should be 1");
    td.check_integer(mem_access_addr, 15'h0010, "Buffered write address mismatch");
    td.check_integer(mem_access_wr_data, 16'hCDEF, "Buffered write data mismatch");
    td.check_integer(mem_access_wr_strb, 2'b11, "Buffered write strobe mismatch");
    mem_access_ready = 1'b1;
    wait_for_resp('0, 1'b0);

    $display("Checking buffered write request abort");
    mem_access_ready = 1'b0;
    fork
      send_write_req(16'h0030, 32'hCAFEBABE, 4'b1100);
      wait_for_write_req(15'h0018, 16'hCAFE, 2'b11);
    join
    td.wait_cycles(2);
    td.check(mem_access_valid, "Write request should still be buffered before abort");
    pulse_abort();
    @(posedge clk);
    td.check(!mem_access_valid, "Write request should be cleared after abort");
    td.wait_cycles(3);
    td.check(!resp_valid, "Abort should not generate a write response");

    $display("Checking immediate read request and error response");
    mem_access_ready = 1'b1;
    fork
      send_read_req(16'h0040);
      wait_for_read_req(15'h0020);
    join
    fork
      pulse_read_data(16'hDEAD, 1'b1);
      wait_for_resp(32'hDEADDEAD, 1'b1);
    join

    $display("Checking buffered read request, then release");
    mem_access_ready = 1'b0;
    fork
      send_read_req(16'h0050);
      wait_for_read_req(15'h0028);
    join
    td.wait_cycles(2);
    td.check(mem_access_valid, "Buffered read request should remain valid while backpressured");
    td.check(!mem_access_wr_en, "Memory write enable should be 0");
    td.check_integer(mem_access_addr, 15'h0028, "Buffered read address mismatch");
    mem_access_ready = 1'b1;
    td.wait_cycles(1);
    fork
      pulse_read_data(16'h0BAD, 1'b0);
      wait_for_resp(32'h0BAD0BAD, 1'b0);
    join

    $display("Checking buffered read request abort");
    mem_access_ready = 1'b0;
    fork
      send_read_req(16'h0060);
      wait_for_read_req(15'h0030);
    join
    td.wait_cycles(2);
    td.check(mem_access_valid, "Read request should still be buffered before abort");
    pulse_abort();
    @(posedge clk);
    td.check(!mem_access_valid, "Read request should be cleared after abort");

    td.finish();
  end
endmodule
